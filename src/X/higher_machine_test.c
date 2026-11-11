#include "higher_machine.h"
#include "term.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    const char *name;
    const int64_t *code;
    size_t length;
    const int64_t *answers;
    const size_t *sizes;
    size_t count;
    /* The same program in fragments: a seed, two additions and the query.
        * Empty when a clause of the program mentions a query variable. */
    struct { const int64_t *code; size_t length; } pieces[4];
} TestCase;

#include "higher_machine_test_fixtures.h"

static size_t allocation_count, fail_at;
void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void *__wrap_malloc(size_t count)
{
    return ++allocation_count == fail_at ? NULL : __real_malloc(count);
}
void *__wrap_calloc(size_t count, size_t width)
{
    return ++allocation_count == fail_at ? NULL : __real_calloc(count, width);
}
void *__wrap_realloc(void *old, size_t count)
{
    return ++allocation_count == fail_at ? NULL : __real_realloc(old, count);
}

/* Every scenario also runs with a collection before each goal. */
static int collect_always;

static HolV2Machine *create(const TestCase *test)
{
    HolV2Machine *machine = hol_v2_create(test->code, test->length);
    if (machine && collect_always) hol_v2_set_collection_step(machine, 0);
    return machine;
}

static int next_answer(HolV2Machine *machine)
{
    for (size_t steps = 0; steps < 10000; ++steps) {
        int status = hol_v2_next(machine);
        if (status == 2) continue;
        if (status != 3) return status;
        int64_t info[6];
        if (hol_v2_event_info(machine, info, 6) < 0) return -1;
        int64_t empty[] = { 0 };
        int result = info[0] == HV2_EVENT_EQUALITY ? 4 : 1;
        if (hol_v2_resume(machine, result, 0, 0, empty, 1) < 0) return -1;
    }
    assert(!"native search exceeded its test budget");
    return -1;
}

/* 1 when the machine gave every answer and then none; 0 otherwise, which only
    * an injected failure may cause. */
static int answers(const TestCase *test, HolV2Machine *machine, int injected)
{
    size_t answer = 0, offset = 0;
    int status;
    while ((status = next_answer(machine)) == 1) {
        size_t count = hol_v2_answer_size(machine);
        int64_t *words = malloc((count ? count : 1) * sizeof(*words));
        if (!words) { assert(injected); return 0; }
        if (hol_v2_answer(machine, words, count) < 0) { free(words); status = -1; break; }
        if (!injected) {
            if (answer >= test->count || test->sizes[answer] != count || memcmp(words, test->answers + offset, count * sizeof(*words))) {
                fprintf(stderr, "%s: answer %zu mismatch:", test->name, answer);
                for (size_t i = 0; i < count; ++i) fprintf(stderr, " %lld", (long long) words[i]);
                fputc('\n', stderr);
                abort();
            }
        }
        offset += count;
        ++answer;
        free(words);
    }
    if (!injected) {
        if (status < 0) fprintf(stderr, "%s: %s\n", test->name, hol_v2_error(machine));
        assert(status == 0 && answer == test->count);
    }
    return status == 0;
}

static int check(const TestCase *test, int injected)
{
    HolV2Machine *machine = create(test);
    if (!machine) { assert(injected); return 0; }
    int complete = answers(test, machine, injected);
    hol_v2_destroy(machine);
    return complete;
}

/* A program given in fragments answers as the whole program does, every time
    * its query runs: after a complete run, and after a run that was left early.
    * Leaving a run gives back its heap and its identities, and ends the life
    * of its snapshots. */
static int fragments(const TestCase *test, int injected)
{
    if (!test->pieces[3].length) return 1;
    HolV2Machine *machine = hol_v2_create(test->pieces[0].code, test->pieces[0].length);
    if (!machine) { assert(injected); return 0; }
    int complete = hol_v2_extend(machine, test->pieces[1].code, test->pieces[1].length) == 1
        && hol_v2_extend(machine, test->pieces[2].code, test->pieces[2].length) == 1;
    size_t heap = hol_v2_heap_count(machine);
    uint64_t frontier = hol_v2_uid_frontier(machine);
    if (complete) assert(hol_v2_next(machine) == 0);
    for (int round = 0; complete && round < (collect_always ? 1 : 3); ++round) {
        complete = hol_v2_query(machine, test->pieces[3].code, test->pieces[3].length) == 1;
        if (complete && round == 1) {
            hol_v2_next(machine);
            HolV2Machine *during = hol_v2_clone(machine);
            complete = hol_v2_query(machine, test->pieces[3].code, test->pieces[3].length) == 1;
            if (during && complete) assert(hol_v2_restore(machine, during) < 0);
            hol_v2_destroy(during);
        }
        if (complete && collect_always) hol_v2_set_collection_step(machine, 0);
        complete = complete && answers(test, machine, injected);
    }
    complete = complete && hol_v2_idle(machine) == 1;
    if (complete) assert(hol_v2_heap_count(machine) == heap && hol_v2_uid_frontier(machine) == frontier && hol_v2_next(machine) == 0);
    if (!injected && !complete) {
        fprintf(stderr, "%s in fragments: %s\n", test->name, hol_v2_error(machine));
        abort();
    }
    hol_v2_destroy(machine);
    return complete;
}

/* A machine created with a query keeps the variables of that query in its
    * program: a later query numbers its own after them, every time. */
static void later_query(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    uint64_t own = (uint64_t) test->code[5];
    assert(machine && own && test->pieces[3].length && answers(test, machine, 0));
    for (int round = 0; round < 2; ++round) {
        assert(hol_v2_query(machine, test->pieces[3].code, test->pieces[3].length) == 1 && hol_v2_uid_frontier(machine) == 2 * own);
        if (collect_always) hol_v2_set_collection_step(machine, 0);
        assert(answers(test, machine, 0));
    }
    assert(hol_v2_idle(machine) == 1 && hol_v2_uid_frontier(machine) == own);
    hol_v2_destroy(machine);
}

/* A fragment that does not fit its machine leaves the machine in error. */
static void malformed_fragments(const TestCase *test)
{
    assert(test->pieces[3].length);
    for (int piece = 1; piece < 4; ++piece) {
        for (size_t position = 2; position < 8; ++position) {
            if (position == 7) continue;
            HolV2Machine *machine = hol_v2_create(test->pieces[0].code, test->pieces[0].length);
            assert(machine);
            if (piece == 3) assert(hol_v2_extend(machine, test->pieces[1].code, test->pieces[1].length) == 1 && hol_v2_extend(machine, test->pieces[2].code, test->pieces[2].length) == 1);
            size_t length = test->pieces[piece].length;
            int64_t *code = malloc(length * sizeof(*code));
            assert(code);
            memcpy(code, test->pieces[piece].code, length * sizeof(*code));
            code[position] = position == 6 && piece < 3 ? 0 : position == 3 ? 0 : code[position] + 1;
            int loaded = piece == 3 ? hol_v2_query(machine, code, length) : hol_v2_extend(machine, code, length);
            if (loaded != -1 || !hol_v2_error(machine)[0] || hol_v2_next(machine) != -1 || hol_v2_idle(machine) != -1) {
                fprintf(stderr, "%s: fragment %d with word %zu changed was accepted\n", test->name, piece, position);
                abort();
            }
            hol_v2_destroy(machine);
            free(code);
        }
    }
}

/* The goal is the last row of a long table: the first step answers, where a
    * scan of the table would have yielded first. */
static void indexed_table(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine && hol_v2_next(machine) == 1 && next_answer(machine) == 0);
    hol_v2_destroy(machine);
}

static void snapshots(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    HolV2Machine *before = hol_v2_clone(machine);
    assert(before);
    assert(next_answer(machine) == 1);
    assert(next_answer(machine) == 1);
    assert(next_answer(machine) == 0);
    assert(hol_v2_restore(machine, before) == 1);
    assert(next_answer(machine) == 1);
    size_t count = hol_v2_answer_size(machine);
    int64_t *answer = malloc(count * sizeof(*answer));
    assert(answer && hol_v2_answer(machine, answer, count) == 1);
    assert(count == test->sizes[0] && !memcmp(answer, test->answers, count * sizeof(*answer)));
    free(answer);
    assert(next_answer(machine) == 1);
    assert(hol_v2_restore(machine, before) == 1);
    assert(next_answer(machine) == 1);
    int64_t assignment[] = { 1, 0, 0, 0, 0, -1, 1, test->answers[test->sizes[0] + 2], -1 };
    assert(hol_v2_assign(machine, assignment, sizeof(assignment) / sizeof(*assignment)) == 1);
    assert(next_answer(machine) == 1);
    count = hol_v2_answer_size(machine);
    answer = malloc(count * sizeof(*answer));
    assert(answer && hol_v2_answer(machine, answer, count) == 1);
    assert(count == test->sizes[1] && !memcmp(answer, test->answers + test->sizes[0], count * sizeof(*answer)));
    free(answer);
    assert(next_answer(machine) == 0);
    assert(hol_v2_restore(machine, before) == 1);
    assert(next_answer(machine) == 1);
    assert(next_answer(machine) == 1);
    assert(next_answer(machine) == 0);
    HolV2Machine *other = create(test);
    assert(other && hol_v2_restore(other, before) < 0);
    assert(hol_v2_error(other)[0] && next_answer(other) == 1);
    hol_v2_destroy(other);
    hol_v2_destroy(before);
    hol_v2_destroy(machine);
}

static void before_cut(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    HolV2Machine *before = hol_v2_clone(machine);
    assert(before);
    assert(next_answer(machine) == 1 && next_answer(machine) == 0);
    assert(hol_v2_restore(machine, before) == 1);
    assert(next_answer(machine) == 1 && next_answer(machine) == 0);
    hol_v2_destroy(before);
    hol_v2_destroy(machine);
}

static void snapshot_stale_uid(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    HolV2Machine *before = hol_v2_clone(machine);
    assert(before && next_answer(machine) == 1);
    assert(hol_v2_restore(machine, before) == 1);
    hol_v2_set_debugging(machine, 1);
    int status;
    do { status = hol_v2_next(machine); } while (status == 2);
    assert(status == 3);
    int64_t stale[] = { 1, 0, 1, 0, 1, -1, 0, 1, 0, 1, -1 };
    assert(hol_v2_resume(machine, 1, 0, 0, stale, sizeof(stale) / sizeof(*stale)) < 0);
    assert(strstr(hol_v2_error(machine), "expired identity"));
    hol_v2_destroy(before);
    hol_v2_destroy(machine);
}

static void dynamic_opaque(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    HolV2Machine *before = hol_v2_clone(machine);
    assert(before);
    size_t symbol = (size_t) test->code[3];
    assert(hol_v2_ensure_symbol(machine, symbol, HV2_PRESBURGER) == 1);
    int64_t binding[] = { 1, 0, 0, 0, 0, -1, 1, (int64_t) symbol, -1 };
    hol_v2_set_debugging(machine, 1);
    assert(hol_v2_next(machine) == 3);
    assert(hol_v2_resume(machine, 1, 0, 0, binding, sizeof(binding) / sizeof(*binding)) == 1);
    assert(next_answer(machine) == 0);
    assert(hol_v2_restore(machine, before) == 1);
    assert(hol_v2_next(machine) == 3);
    assert(hol_v2_resume(machine, 1, 0, 0, binding, sizeof(binding) / sizeof(*binding)) == 1);
    assert(next_answer(machine) == 0);
    assert(hol_v2_restore(machine, before) == 1);
    hol_v2_set_debugging(machine, 0);
    assert(hol_v2_assign(machine, binding, sizeof(binding) / sizeof(*binding)) == 1);
    assert(next_answer(machine) == 1);
    size_t count = hol_v2_answer_size(machine);
    int64_t answer[4];
    assert(count == 4 && hol_v2_answer(machine, answer, 4) == 1);
    assert(answer[0] == 1 && answer[1] == 1 && answer[2] == (int64_t) symbol);
    hol_v2_destroy(before);
    hol_v2_destroy(machine);
}

static void work_limits(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine && hol_v2_work_limit(machine) == 5000000);
    HolV2Machine *before = hol_v2_clone(machine);
    assert(before);
    assert(hol_v2_set_work_limit(machine, 0) < 0);
    assert(hol_v2_set_work_limit(machine, 1) == 1);
    assert(next_answer(machine) < 0);
    assert(strstr(hol_v2_error(machine), "work") || strstr(hol_v2_error(machine), "budget"));
    assert(hol_v2_set_work_limit(machine, 5000000) == 1);
    assert(hol_v2_restore(machine, before) == 1);
    assert(hol_v2_work_limit(machine) == 5000000);
    assert(hol_v2_set_work_limit(machine, 3000000) == 1);
    assert(hol_v2_restore(machine, before) == 1);
    assert(hol_v2_work_limit(machine) == 3000000);
    assert(next_answer(machine) == 1);
    hol_v2_destroy(before);
    hol_v2_destroy(machine);
}

static void malformed(const TestCase *test)
{
    int64_t *code = malloc(test->length * sizeof(*code));
    assert(code);
    const size_t positions[] = { 0, 1, 2, 3, 4, 5, 6, 7 };
    for (size_t i = 0; i < sizeof(positions) / sizeof(*positions); ++i) {
        memcpy(code, test->code, test->length * sizeof(*code));
        code[positions[i]] = -1;
        HolV2Machine *machine = hol_v2_create(code, test->length);
        assert(machine && hol_v2_next(machine) < 0);
        hol_v2_destroy(machine);
    }
    memcpy(code, test->code, test->length * sizeof(*code));
    code[8] = 0;
    HolV2Machine *machine = hol_v2_create(code, test->length);
    assert(machine && hol_v2_next(machine) < 0);
    hol_v2_destroy(machine);
    machine = hol_v2_create(NULL, 0);
    assert(machine && hol_v2_next(machine) < 0);
    hol_v2_destroy(machine);
    free(code);
}

static void snapshot_allocations(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    allocation_count = 0;
    HolV2Machine *snapshot = hol_v2_clone(machine);
    assert(snapshot);
    size_t allocations = allocation_count;
    hol_v2_destroy(snapshot);
    hol_v2_destroy(machine);
    for (size_t i = 1; i <= allocations; ++i) {
        machine = create(test);
        assert(machine);
        allocation_count = 0;
        fail_at = i;
        snapshot = hol_v2_clone(machine);
        fail_at = 0;
        hol_v2_destroy(snapshot);
        assert(next_answer(machine) == 1);
        hol_v2_destroy(machine);
    }
    printf("PASS snapshot allocation cleanup (%zu failure points)\n", allocations);
}

static void yielded_search(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    assert(hol_v2_next(machine) == 2);
    HolV2Machine *during = hol_v2_clone(machine);
    assert(during);
    assert(next_answer(machine) == 1 && next_answer(machine) == 0);
    assert(hol_v2_restore(machine, during) == 1);
    assert(next_answer(machine) == 1 && next_answer(machine) == 0);
    hol_v2_destroy(during);
    hol_v2_destroy(machine);
}

static void yielded_backtracking(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    int status;
    do { status = hol_v2_next(machine); } while (status == 2);
    assert(status == 3);
    int64_t info[6], empty[] = { 0 };
    assert(hol_v2_event_info(machine, info, 6) == 1 && info[0] == HV2_EVENT_PRIMITIVE);
    assert(hol_v2_resume(machine, 0, 0, 0, empty, 1) == 1);
    assert(hol_v2_next(machine) == 2);
    HolV2Machine *during = hol_v2_clone(machine);
    assert(during);
    assert(next_answer(machine) == 0);
    assert(hol_v2_restore(machine, during) == 1);
    assert(next_answer(machine) == 0);
    hol_v2_destroy(during);
    hol_v2_destroy(machine);
}

/* The machine decides an equality without arithmetic and an implication whose
    * antecedent gives the host no premise; every other one raises its event. */
static const struct { const char *name; int kind; size_t count; } host_events[] = {
    { "plain_equality", HV2_EVENT_EQUALITY, 0 },
    { "natural_equality", HV2_EVENT_EQUALITY, 1 },
    { "arithmetic_equality", HV2_EVENT_EQUALITY, 1 },
    { "successor_equality", HV2_EVENT_EQUALITY, 1 },
    { "bound_arithmetic_equality", HV2_EVENT_EQUALITY, 2 },
    { "opaque_equality", HV2_EVENT_EQUALITY, 1 },
    { "local_equality_precedence", HV2_EVENT_EQUALITY, 0 },
    { "local_equality_precedence", HV2_EVENT_IMPLY, 1 },
    { "stable_bottom_up_list", HV2_EVENT_EQUALITY, 0 },
    { "plain_antecedent", HV2_EVENT_IMPLY, 0 },
    { "quantified_antecedent", HV2_EVENT_IMPLY, 1 },
    { "comparison_antecedent", HV2_EVENT_IMPLY, 1 },
};

static void raised_events(const TestCase *test)
{
    for (size_t i = 0; i < sizeof(host_events) / sizeof(*host_events); ++i) {
        if (strcmp(test->name, host_events[i].name)) continue;
        HolV2Machine *machine = create(test);
        assert(machine);
        size_t count = 0;
        for (;;) {
            int status = hol_v2_next(machine);
            if (status == 1 || status == 2) continue;
            if (status != 3) { assert(status == 0); break; }
            int64_t info[6], empty[] = { 0 };
            assert(hol_v2_event_info(machine, info, 6) == 1);
            if (info[0] == host_events[i].kind) ++count;
            assert(hol_v2_resume(machine, info[0] == HV2_EVENT_EQUALITY ? 4 : 1, 0, 0, empty, 1) == 1);
        }
        if (count != host_events[i].count) {
            fprintf(stderr, "%s: %zu events of kind %d\n", test->name, count, host_events[i].kind);
            abort();
        }
        hol_v2_destroy(machine);
    }
}

static void bounded_work(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine && hol_v2_set_work_limit(machine, 256) == 1);
    assert(next_answer(machine) == 1 && next_answer(machine) == 0);
    hol_v2_destroy(machine);
}

static void excluded_natural(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    uint64_t before = hol_v2_uid_frontier(machine);
    assert(next_answer(machine) == 1 && hol_v2_uid_frontier(machine) == before + 1);
    assert(next_answer(machine) == 0 && hol_v2_uid_frontier(machine) == before + 1);
    hol_v2_destroy(machine);
}

static void excluded_choice(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    int status;
    do { status = hol_v2_next(machine); } while (status == 2);
    assert(status == 3);
    int64_t info[6], empty[] = { 0 };
    assert(hol_v2_event_info(machine, info, 6) == 1 && info[0] == HV2_EVENT_PRIMITIVE);
    assert(hol_v2_resume(machine, 0, 0, 0, empty, 1) == 1);
    assert(hol_v2_next(machine) == 0);
    hol_v2_destroy(machine);
}

static void collected_descent(const TestCase *test)
{
    HolV2Machine *machine = hol_v2_create(test->code, test->length);
    assert(machine);
    size_t program = hol_v2_heap_count(machine);
    hol_v2_set_collection_step(machine, 1024);
    assert(next_answer(machine) == 1);
    assert(hol_v2_collections(machine) > 8 && hol_v2_heap_count(machine) < program + 4096);
    assert(next_answer(machine) == 0);
    hol_v2_destroy(machine);
}

static void collect_term_declarations(const int64_t *wire, size_t length, size_t *offset, int64_t *output, size_t *used)
{
    size_t remaining = 1;
    while (remaining) {
        assert(*offset < length);
        size_t start = (*offset)++;
        int64_t tag = wire[start];
        --remaining;
        size_t fields;
        switch (tag) {
            case HT_VAR: fields = 4; break;
            case HT_NOMINAL: fields = 3; break;
            case HT_CONST: fields = 2; break;
            case HT_APP: fields = 1; remaining += 2; break;
            case HT_LAM: fields = 1; ++remaining; break;
            case HT_INDEX: fields = 1; break;
            case HT_WILD: fields = 0; break;
            case HT_NAT:
                assert(*offset < length && wire[*offset] > 0);
                fields = 1 + (size_t) wire[*offset];
                break;
            default: assert(!"invalid term wire"); return;
        }
        assert(fields <= length - *offset);
        *offset += fields;
        if (tag == HT_VAR || tag == HT_NOMINAL) {
            ++output[0];
            for (size_t i = start; i < *offset; ++i) output[(*used)++] = wire[i];
        }
    }
}

static void compact_declarations(const TestCase *test)
{
    HolV2Machine *machine = create(test);
    assert(machine);
    for (;;) {
        int status = hol_v2_next(machine);
        if (status == 2) continue;
        assert(status == 3);
        int64_t info[6], empty[] = { 0 };
        assert(hol_v2_event_info(machine, info, 6) == 1);
        if (info[0] == HV2_EVENT_PRIMITIVE) break;
        assert(hol_v2_resume(machine, 1, 0, 0, empty, 1) == 1);
    }
    HolV2Machine *before = hol_v2_clone(machine);
    assert(before);
    size_t frames = hol_v2_frames_size(machine);
    int64_t *wire = malloc(frames * sizeof(*wire));
    int64_t *expected = malloc(frames * sizeof(*expected));
    int64_t *actual = malloc(frames * sizeof(*actual));
    assert(wire && expected && actual);
    assert(hol_v2_frames(machine, wire, frames) == 1);
    expected[0] = 0;
    size_t offset = 1, words = 1;
    for (int64_t i = 0; i < wire[0]; ++i) {
        assert(frames - offset >= 3);
        size_t hypotheses = (size_t) wire[offset + 2];
        offset += 3;
        for (size_t j = 0; j <= hypotheses; ++j) {
            collect_term_declarations(wire, frames, &offset, expected, &words);
        }
    }
    assert(offset == frames && expected[0] == 8 && frames > words);
    assert(hol_v2_declarations_size(machine) == words);
    assert(hol_v2_declarations(machine, actual, words) == 1);
    assert(!memcmp(actual, expected, words * sizeof(*expected)));
    assert(hol_v2_restore(machine, before) == 1);
    assert(hol_v2_declarations_size(machine) == words);
    assert(hol_v2_declarations(machine, actual, words) == 1);
    assert(!memcmp(actual, expected, words * sizeof(*expected)));
    hol_v2_destroy(machine);
    free(wire);
    free(expected);
    free(actual);

    machine = hol_v2_clone(before);
    assert(machine);
    allocation_count = 0;
    fail_at = SIZE_MAX;
    assert(hol_v2_declarations_size(machine) == words);
    size_t allocations = allocation_count;
    fail_at = 0;
    hol_v2_destroy(machine);
    for (size_t i = 1; i <= allocations; ++i) {
        machine = hol_v2_clone(before);
        assert(machine);
        allocation_count = 0;
        fail_at = i;
        assert(hol_v2_declarations_size(machine) == 0);
        fail_at = 0;
        assert(*hol_v2_error(machine));
        hol_v2_destroy(machine);
    }
    hol_v2_destroy(before);
    printf("PASS compact metadata allocation cleanup (%zu failure points)\n", allocations);
}

static void scenarios(void)
{
    size_t count = sizeof(cases) / sizeof(*cases);
    for (size_t i = 0; i < count; ++i) {
        check(&cases[i], 0);
        /* The walk keeps a choice point for each of its 5000 levels: with a
            * collection before each goal one run of it is enough. */
        if (!collect_always || strcmp(cases[i].name, "yield_failed_backtracking")) fragments(&cases[i], 0);
        raised_events(&cases[i]);
        if (!strcmp(cases[i].name, "indexed_natural_table")) indexed_table(&cases[i]);
        if (!strcmp(cases[i].name, "indexed_constant_table")) indexed_table(&cases[i]);
        if (!strcmp(cases[i].name, "yielded_clause_search")) yielded_search(&cases[i]);
        if (!strcmp(cases[i].name, "yielded_equality_resume")) yielded_search(&cases[i]);
        if (!strcmp(cases[i].name, "yield_failed_backtracking")) yielded_backtracking(&cases[i]);
        if (!strcmp(cases[i].name, "stable_bottom_up_list")) bounded_work(&cases[i]);
        if (!strcmp(cases[i].name, "excluded_natural_clause")) excluded_natural(&cases[i]);
        if (!strcmp(cases[i].name, "excluded_clause_choice")) excluded_choice(&cases[i]);
        if (!strcmp(cases[i].name, "collected_descent")) collected_descent(&cases[i]);
        if (!strcmp(cases[i].name, "compact_frame_declarations")) compact_declarations(&cases[i]);
        printf("PASS %s\n", cases[i].name);
    }
    snapshots(&cases[count - 2]);
    before_cut(&cases[count - 1]);
    snapshot_stale_uid(&cases[count - 2]);
    dynamic_opaque(&cases[count - 3]);
    work_limits(&cases[0]);
    puts("PASS native snapshots, restore, cut and persistent assignment");
    malformed(&cases[0]);
    puts("PASS malformed native wordcode");
    snapshot_allocations(&cases[count - 2]);
    allocation_count = 0;
    check(&cases[1], 0);
    size_t allocations = allocation_count;
    for (size_t i = 1; i <= allocations; ++i) {
        allocation_count = 0;
        fail_at = i;
        check(&cases[1], 1);
    }
    fail_at = 0;
    printf("PASS native allocation cleanup (%zu failure points)\n", allocations);
    const TestCase *split = NULL;
    for (size_t i = 0; i < count; ++i) if (!strcmp(cases[i].name, "predicate_cut")) split = &cases[i];
    assert(split);
    malformed_fragments(split);
    later_query(split);
    allocation_count = 0;
    fragments(split, 0);
    allocations = allocation_count;
    for (size_t i = 1; i <= allocations; ++i) {
        allocation_count = 0;
        fail_at = i;
        fragments(split, 1);
    }
    fail_at = 0;
    printf("PASS native fragments: malformed ones, allocation cleanup (%zu failure points)\n", allocations);
}

int main(void)
{
    scenarios();
    collect_always = 1;
    scenarios();
    puts("PASS every scenario with a collection before each goal");
    return 0;
}

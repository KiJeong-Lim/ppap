#include "machine.h"

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
} TestCase;

#include "machine_test_fixtures.h"

static size_t fail_at, allocation_count, yield_count;

void *__real_calloc(size_t count, size_t width);
void *__real_realloc(void *old, size_t count);

void *__wrap_calloc(size_t count, size_t width)
{
    return fail_at && ++allocation_count == fail_at ? NULL : __real_calloc(count, width);
}

void *__wrap_realloc(void *old, size_t count)
{
    return fail_at && ++allocation_count == fail_at ? NULL : __real_realloc(old, count);
}

static int next_answer(HolV1Machine *machine)
{
    int status;
    while ((status = hol_v1_next(machine)) == 2) {
        ++yield_count;
    }
    return status;
}

static void normalize_variables(int64_t *answer, size_t count, size_t query_slots)
{
    int64_t *variables = malloc((count + 1) * sizeof(*variables));
    assert(variables);
    size_t used = 0;
    for (size_t i = 0; i < count;) {
        int64_t tag = answer[i++];
        if (tag == 2) {
            continue;
        }
        assert((tag == 0 || tag == 1) && i < count);
        if (tag == 0 && answer[i] >= (int64_t) query_slots) {
            size_t index = 0;
            while (index < used && variables[index] != answer[i]) {
                ++index;
            }
            if (index == used) {
                variables[used++] = answer[i];
            }
            answer[i] = (int64_t) (query_slots + index);
        }
        ++i;
    }
    free(variables);
}

static void check(const TestCase *test)
{
    HolV1Machine *machine = hol_v1_create(test->code, test->length);
    assert(machine);
    size_t offset = 0;
    for (size_t i = 0; i < test->count; ++i) {
        int status = next_answer(machine);
        if (status != 1) {
            fprintf(stderr, "%s: status %d: %s\n", test->name, status, hol_v1_error(machine));
            abort();
        }
        size_t count = hol_v1_answer_size(machine);
        assert(count == test->sizes[i]);
        int64_t *output = malloc((count + 1) * sizeof(*output));
        assert(output);
        assert(hol_v1_answer(machine, output, count) == 1);
        int64_t *expected = malloc((count + 1) * sizeof(*expected));
        assert(expected);
        memcpy(expected, test->answers + offset, count * sizeof(*expected));
        normalize_variables(output, count, (size_t) test->code[5]);
        normalize_variables(expected, count, (size_t) test->code[5]);
        assert(memcmp(output, expected, count * sizeof(*output)) == 0);
        offset += count;
        free(expected);
        free(output);
    }
    assert(next_answer(machine) == 0);
    assert(next_answer(machine) == 0);
    hol_v1_destroy(machine);
    printf("PASS %s\n", test->name);
}

static void reject(const int64_t *code, size_t length)
{
    HolV1Machine *machine = hol_v1_create(code, length);
    assert(machine);
    assert(hol_v1_next(machine) == -1);
    assert(*hol_v1_error(machine));
    hol_v1_destroy(machine);
}

static int run_fault_case(const TestCase *test)
{
    HolV1Machine *machine = hol_v1_create(test->code, test->length);
    int status = -1;
    if (machine) {
        while ((status = next_answer(machine)) == 1) {
        }
        assert(status == 0 || (status == -1 && *hol_v1_error(machine)));
        hol_v1_destroy(machine);
    }
    return status;
}

static void check_allocation_failures(const TestCase *test)
{
    fail_at = SIZE_MAX;
    allocation_count = 0;
    assert(run_fault_case(test) == 0);
    size_t total = allocation_count;
    for (size_t fault = 1; fault <= total; ++fault) {
        fail_at = fault;
        allocation_count = 0;
        assert(run_fault_case(test) == -1);
        assert(allocation_count >= fault);
    }
    fail_at = 0;
    printf("PASS %s allocation cleanup (%zu failure points)\n", test->name, total);
}

int main(void)
{
    for (size_t i = 0; i < sizeof(cases) / sizeof(*cases); ++i) {
        check(&cases[i]);
        if (!strcmp(cases[i].name, "recursive_member") || !strcmp(cases[i].name, "deep_term") || !strcmp(cases[i].name, "clause_application_spine") || !strcmp(cases[i].name, "body_only_choice_rollback") || !strcmp(cases[i].name, "head_subtree_shared_variable")) {
            check_allocation_failures(&cases[i]);
        }
    }
    assert(yield_count > 0);

    int64_t minimal[] = { 0x484f4c31, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 };
    reject(NULL, 0);
    for (size_t count = 0; count < 12; ++count) {
        reject(minimal, count);
    }
    minimal[1] = 2;
    reject(minimal, 12);
    minimal[1] = 1;
    minimal[5] = INT64_MAX;
    reject(minimal, 12);
    minimal[5] = 0;
    minimal[9] = -1;
    reject(minimal, 12);
    minimal[9] = 0;

    HolV1Machine *copy = hol_v1_create(minimal, 12);
    assert(copy);
    minimal[8] = 1;
    assert(hol_v1_next(copy) == 1);
    hol_v1_destroy(copy);
    minimal[8] = 0;

    int64_t malformed[] = { 0x484f4c31, 1, 1, 2, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0 };
    reject(malformed, 19);
    malformed[9] = 0;
    malformed[8] = 2;
    reject(malformed, 19);
    malformed[8] = 0;
    malformed[10] = 1;
    reject(malformed, 19);
    malformed[10] = 0;
    malformed[17] = 1;
    reject(malformed, 19);
    puts("PASS malformed_and_input_copy");

    minimal[8] = 5;
    HolV1Machine *loop = hol_v1_create(minimal, 12);
    assert(loop);
    assert(hol_v1_next(loop) == 2);
    assert(hol_v1_next(loop) == 2);
    hol_v1_destroy(loop);
    puts("PASS cooperative_yield");
    return 0;
}

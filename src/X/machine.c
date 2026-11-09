#include "machine.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define NONE SIZE_MAX
enum { TERM_VAR, TERM_CONST, TERM_APP };
enum { OP_RETURN, OP_FAIL, OP_CALL, OP_UNIFY, OP_CHOICE, OP_CUT };
enum { CHOICE_CODE, CHOICE_CLAUSE };

typedef struct { size_t a, b, slots, constant; int tag; } Template;
typedef struct { size_t a, b, c; int op; } Instruction;
typedef struct { size_t symbol, slots, head, entry, next; } Clause;
typedef struct { size_t symbol, first; } Predicate;
typedef struct { size_t a, b; uint64_t seen; int tag; } Node;
typedef struct { size_t pc, env, slots, barrier, continuation; } State;
typedef struct { size_t heap, env, trail, work; } Checkpoint;
typedef struct { size_t term, left; int stage; } BuildFrame;
typedef struct { size_t left, right; } Pair;
typedef struct {
    Checkpoint checkpoint;
    State state;
    size_t goal, clause, continuation, barrier;
    int kind;
} Choice;

struct HolV1Machine {
    Template *terms;
    Instruction *instructions;
    Clause *clauses;
    Predicate *predicates;
    size_t term_count, instruction_count, clause_count, predicate_capacity;
    size_t query_slots, symbol_count;
    Node *heap;
    size_t heap_count, heap_capacity;
    size_t *env, *trail, *scratch;
    size_t env_count, env_capacity, trail_count, trail_capacity, scratch_capacity;
    State *work;
    size_t work_count, work_capacity;
    Choice *choices;
    size_t choice_count, choices_capacity;
    BuildFrame *build;
    size_t build_capacity;
    Pair *pairs, *matches;
    size_t pairs_capacity, matches_capacity;
    int64_t *answer;
    size_t answer_count, answer_capacity;
    uint64_t visit;
    State state;
    int answer_ready, resume, exhausted;
    char error[192];
};

static int fail(HolV1Machine *m, const char *message)
{
    if (!m->error[0]) {
        size_t length = strlen(message);
        if (length >= sizeof(m->error)) {
            length = sizeof(m->error) - 1;
        }
        memcpy(m->error, message, length);
        m->error[length] = '\0';
    }
    return 0;
}

static void *allocate(HolV1Machine *m, size_t count, size_t width)
{
    if (!count) {
        return NULL;
    }
    if (count > SIZE_MAX / width) {
        fail(m, "VM allocation size overflow");
        return NULL;
    }
    void *result = calloc(count, width);
    if (!result) {
        fail(m, "VM allocation failed");
    }
    return result;
}

static void *grow(HolV1Machine *m, void *old, size_t *capacity, size_t count, size_t width)
{
    if (count <= *capacity) {
        return old;
    }
    if (count > SIZE_MAX / width) {
        fail(m, "VM allocation size overflow");
        return NULL;
    }
    size_t next = *capacity ? *capacity : 64;
    while (next < count) {
        if (next > SIZE_MAX / 2) {
            next = count;
            break;
        }
        next *= 2;
    }
    if (next > SIZE_MAX / width) {
        next = count;
    }
    void *result = realloc(old, next * width);
    if (!result) {
        fail(m, "VM allocation failed");
        return NULL;
    }
    *capacity = next;
    return result;
}

#define ENSURE(m, field, count) do { \
    void *resized = grow((m), (m)->field, &(m)->field##_capacity, (count), sizeof(*(m)->field)); \
    if (!resized) { \
        return 0; \
    } \
    (m)->field = resized; \
} while (0)

static int push_node(HolV1Machine *m, int tag, size_t a, size_t b, size_t *result)
{
    if (m->heap_count >= INT64_MAX || m->heap_count == SIZE_MAX) {
        return fail(m, "VM term index overflow");
    }
    ENSURE(m, heap, m->heap_count + 1);
    *result = m->heap_count;
    m->heap[m->heap_count++] = (Node) { a, b, 0, tag };
    return 1;
}

static int new_environment(HolV1Machine *m, size_t slots, size_t *base, int eager)
{
    if (slots > SIZE_MAX - m->env_count) {
        return fail(m, "VM environment size overflow");
    }
    *base = m->env_count;
    if (slots) {
        ENSURE(m, env, m->env_count + slots);
    }
    for (size_t i = 0; i < slots; ++i) {
        size_t variable = NONE;
        if (eager && !push_node(m, TERM_VAR, NONE, 0, &variable)) {
            return 0;
        }
        m->env[m->env_count++] = variable;
    }
    return 1;
}

static Checkpoint checkpoint(const HolV1Machine *m)
{
    return (Checkpoint) { m->heap_count, m->env_count, m->trail_count, m->work_count };
}

static void restore(HolV1Machine *m, Checkpoint saved)
{
    while (m->trail_count > saved.trail) {
        m->heap[m->trail[--m->trail_count]].a = NONE;
    }
    m->heap_count = saved.heap;
    m->env_count = saved.env;
    m->work_count = saved.work;
}

static size_t dereference(const HolV1Machine *m, size_t term)
{
    while (m->heap[term].tag == TERM_VAR && m->heap[term].a != NONE) {
        term = m->heap[term].a;
    }
    return term;
}

static int instantiate(HolV1Machine *m, size_t root, size_t env, size_t slots, size_t *result)
{
    if (m->terms[root].slots > slots) {
        return fail(m, "Term refers outside its variable environment");
    }
    ENSURE(m, build, 1);
    size_t count = 1;
    m->build[0] = (BuildFrame) { root, 0, 0 };
    while (count) {
        BuildFrame frame = m->build[count - 1];
        Template term = m->terms[frame.term];
        if (term.tag == TERM_VAR) {
            size_t *variable = &m->env[env + term.a];
            if (*variable == NONE && !push_node(m, TERM_VAR, NONE, 0, variable)) {
                return 0;
            }
            *result = *variable;
            --count;
        } else if (term.tag == TERM_CONST) {
            *result = term.constant;
            --count;
        } else if (frame.stage == 0) {
            m->build[count - 1].stage = 1;
            ENSURE(m, build, count + 1);
            m->build[count++] = (BuildFrame) { term.a, 0, 0 };
        } else if (frame.stage == 1) {
            m->build[count - 1].stage = 2;
            m->build[count - 1].left = *result;
            ENSURE(m, build, count + 1);
            m->build[count++] = (BuildFrame) { term.b, 0, 0 };
        } else {
            if (!push_node(m, TERM_APP, frame.left, *result, result)) {
                return 0;
            }
            --count;
        }
    }
    return 1;
}

/* -1 is allocation failure; 1 is occurrence; 0 is absence. */
static int occurs(HolV1Machine *m, size_t variable, size_t term)
{
    if (++m->visit == 0) {
        for (size_t i = 0; i < m->heap_count; ++i) {
            m->heap[i].seen = 0;
        }
        m->visit = 1;
    }
    void *resized = grow(m, m->scratch, &m->scratch_capacity, 1, sizeof(*m->scratch));
    if (!resized) {
        return -1;
    }
    m->scratch = resized;
    size_t count = 1;
    m->scratch[0] = term;
    while (count) {
        size_t current = dereference(m, m->scratch[--count]);
        if (current == variable) {
            return 1;
        }
        Node *node = &m->heap[current];
        if (node->tag == TERM_APP && node->seen != m->visit) {
            node->seen = m->visit;
            resized = grow(m, m->scratch, &m->scratch_capacity, count + 2, sizeof(*m->scratch));
            if (!resized) {
                return -1;
            }
            m->scratch = resized;
            m->scratch[count++] = node->b;
            m->scratch[count++] = node->a;
        }
    }
    return 0;
}

static int bind_variable(HolV1Machine *m, size_t variable, size_t value)
{
    ENSURE(m, trail, m->trail_count + 1);
    m->trail[m->trail_count++] = variable;
    m->heap[variable].a = value;
    return 1;
}

/* Logical failure is distinguished from allocation failure by m->error. */
static int unify(HolV1Machine *m, size_t left, size_t right)
{
    ENSURE(m, pairs, 1);
    size_t count = 1;
    m->pairs[0] = (Pair) { left, right };
    while (count) {
        Pair pair = m->pairs[--count];
        left = dereference(m, pair.left);
        right = dereference(m, pair.right);
        if (left == right) {
            continue;
        }
        int left_tag = m->heap[left].tag;
        int right_tag = m->heap[right].tag;
        if (left_tag == TERM_VAR && right_tag == TERM_VAR) {
            if (left >= m->query_slots && right >= m->query_slots) {
                size_t newer = left > right ? left : right;
                size_t older = left > right ? right : left;
                if (!bind_variable(m, newer, older)) {
                    return 0;
                }
            } else {
                /* Preserve fresh representatives for initial query-slot projection. */
                size_t common;
                if (!push_node(m, TERM_VAR, NONE, 0, &common) || !bind_variable(m, left, common) || !bind_variable(m, right, common)) {
                    return 0;
                }
            }
        } else if (left_tag == TERM_VAR || right_tag == TERM_VAR) {
            size_t variable = left_tag == TERM_VAR ? left : right;
            size_t value = left_tag == TERM_VAR ? right : left;
            if ((m->heap[value].tag != TERM_CONST && occurs(m, variable, value) != 0) || !bind_variable(m, variable, value)) {
                return 0;
            }
        } else if (left_tag != right_tag) {
            return 0;
        } else if (left_tag == TERM_CONST) {
            if (m->heap[left].a != m->heap[right].a) {
                return 0;
            }
        } else {
            ENSURE(m, pairs, count + 2);
            m->pairs[count++] = (Pair) { m->heap[left].b, m->heap[right].b };
            m->pairs[count++] = (Pair) { m->heap[left].a, m->heap[right].a };
        }
    }
    return 1;
}

/* Match directly; instantiate only a subtree assigned to an unbound goal. */
static int match_clause(HolV1Machine *m, size_t goal, size_t root, size_t env, size_t slots)
{
    ENSURE(m, matches, 1);
    size_t count = 1;
    m->matches[0] = (Pair) { goal, root };
    while (count) {
        Pair pair = m->matches[--count];
        size_t value = dereference(m, pair.left);
        Template term = m->terms[pair.right];
        if (term.tag == TERM_VAR) {
            size_t *variable = &m->env[env + term.a];
            if (*variable == NONE) {
                /* Initial query variables must remain visibly bound to a fresh variable. */
                if (value < m->query_slots && m->heap[value].tag == TERM_VAR) {
                    size_t common;
                    if (!push_node(m, TERM_VAR, NONE, 0, &common) || !bind_variable(m, value, common)) {
                        return 0;
                    }
                    value = common;
                }
                *variable = value;
            } else if (!unify(m, value, *variable)) {
                return 0;
            }
        } else if (term.tag == TERM_CONST) {
            if (m->heap[value].tag == TERM_CONST) {
                if (m->heap[value].a != term.a) {
                    return 0;
                }
            } else if (m->heap[value].tag == TERM_VAR) {
                if (!bind_variable(m, value, term.constant)) {
                    return 0;
                }
            } else {
                return 0;
            }
        } else if (m->heap[value].tag == TERM_VAR) {
            size_t built;
            if (!instantiate(m, pair.right, env, slots, &built) || !unify(m, value, built)) {
                return 0;
            }
        } else if (m->heap[value].tag != TERM_APP) {
            return 0;
        } else {
            ENSURE(m, matches, count + 2);
            m->matches[count++] = (Pair) { m->heap[value].b, term.b };
            m->matches[count++] = (Pair) { m->heap[value].a, term.a };
        }
    }
    return 1;
}

static size_t predicate_bucket(const HolV1Machine *m, size_t symbol)
{
    size_t bucket = (symbol * (size_t) UINT64_C(11400714819323198485)) & (m->predicate_capacity - 1);
    while (m->predicates[bucket].symbol != NONE && m->predicates[bucket].symbol != symbol) {
        bucket = (bucket + 1) & (m->predicate_capacity - 1);
    }
    return bucket;
}

static int push_choice(HolV1Machine *m, Choice choice)
{
    ENSURE(m, choices, m->choice_count + 1);
    m->choices[m->choice_count++] = choice;
    return 1;
}

static int try_clauses(HolV1Machine *m, size_t goal, size_t clause, size_t continuation, size_t barrier, Checkpoint saved)
{
    while (clause != NONE) {
        Clause current = m->clauses[clause];
        size_t env;
        if (!new_environment(m, current.slots, &env, 0)) {
            return 0;
        }
        if (match_clause(m, goal, current.head, env, current.slots)) {
            /* Body choices restore heap indices, so complete the environment before entry. */
            for (size_t i = 0; i < current.slots; ++i) {
                size_t *variable = &m->env[env + i];
                if (*variable == NONE && !push_node(m, TERM_VAR, NONE, 0, variable)) {
                    return 0;
                }
            }
            if (current.next != NONE) {
                Choice choice = { 0 };
                choice.kind = CHOICE_CLAUSE;
                choice.checkpoint = saved;
                choice.goal = goal;
                choice.clause = current.next;
                choice.continuation = continuation;
                choice.barrier = barrier;
                if (!push_choice(m, choice)) {
                    return 0;
                }
            }
            m->state = (State) { current.entry, env, current.slots, barrier, continuation };
            return 1;
        }
        if (m->error[0]) {
            return 0;
        }
        restore(m, saved);
        clause = current.next;
    }
    return 0;
}

static int backtrack(HolV1Machine *m)
{
    while (m->choice_count) {
        Choice choice = m->choices[--m->choice_count];
        restore(m, choice.checkpoint);
        if (choice.kind == CHOICE_CODE) {
            m->state = choice.state;
            return 1;
        }
        if (try_clauses(m, choice.goal, choice.clause, choice.continuation, choice.barrier, choice.checkpoint)) {
            return 1;
        }
        if (m->error[0]) {
            return 0;
        }
    }
    return 0;
}

static int call(HolV1Machine *m, Instruction instruction)
{
    size_t goal;
    if (!instantiate(m, instruction.a, m->state.env, m->state.slots, &goal)) {
        return 0;
    }
    size_t head = dereference(m, goal);
    while (m->heap[head].tag == TERM_APP) {
        head = dereference(m, m->heap[head].a);
    }
    if (m->heap[head].tag != TERM_CONST) {
        return fail(m, "A VM predicate call has an unbound head");
    }
    size_t clause = m->predicates[predicate_bucket(m, m->heap[head].a)].first;
    if (clause == NONE) {
        return 0;
    }
    ENSURE(m, work, m->work_count + 1);
    State next = m->state;
    next.pc = instruction.b;
    size_t continuation = m->work_count;
    m->work[m->work_count++] = next;
    return try_clauses(m, goal, clause, continuation, m->choice_count, checkpoint(m));
}

static int serialize_answer(HolV1Machine *m)
{
    m->answer_count = 0;
    for (size_t slot = 0; slot < m->query_slots; ++slot) {
        ENSURE(m, scratch, 1);
        size_t count = 1;
        m->scratch[0] = m->env[slot];
        while (count) {
            size_t current = dereference(m, m->scratch[--count]);
            Node node = m->heap[current];
            ENSURE(m, answer, m->answer_count + 2);
            m->answer[m->answer_count++] = node.tag;
            if (node.tag == TERM_VAR) {
                m->answer[m->answer_count++] = (int64_t) current;
            } else if (node.tag == TERM_CONST) {
                m->answer[m->answer_count++] = (int64_t) node.a;
            } else {
                ENSURE(m, scratch, count + 2);
                m->scratch[count++] = node.b;
                m->scratch[count++] = node.a;
            }
        }
    }
    m->answer_ready = 1;
    return 1;
}

static int index_in(int64_t value, size_t count)
{
    return value >= 0 && (uint64_t) value < count;
}

static int validate_context(HolV1Machine *m, size_t entry, size_t slots, size_t *visited, size_t stamp)
{
    ENSURE(m, scratch, 1);
    size_t count = 1;
    m->scratch[0] = entry;
    while (count) {
        size_t pc = m->scratch[--count];
        if (visited[pc] == stamp) {
            continue;
        }
        visited[pc] = stamp;
        Instruction instruction = m->instructions[pc];
        if ((instruction.op == OP_CALL || instruction.op == OP_UNIFY) && m->terms[instruction.a].slots > slots) {
            return fail(m, "Instruction refers outside its variable environment");
        }
        if (instruction.op == OP_UNIFY && m->terms[instruction.b].slots > slots) {
            return fail(m, "Instruction refers outside its variable environment");
        }
        ENSURE(m, scratch, count + 2);
        switch (instruction.op) {
            case OP_CALL:
                m->scratch[count++] = instruction.b;
                break;
            case OP_UNIFY:
                m->scratch[count++] = instruction.c;
                break;
            case OP_CHOICE:
                m->scratch[count++] = instruction.a;
                m->scratch[count++] = instruction.b;
                break;
            case OP_CUT:
                m->scratch[count++] = instruction.a;
                break;
            default:
                break;
        }
    }
    return 1;
}

HolV1Machine *hol_v1_create(const int64_t *code, size_t length)
{
    HolV1Machine *m = calloc(1, sizeof(*m));
    if (!m) {
        return NULL;
    }
    if (!code || length < 8 || code[0] != INT64_C(0x484f4c31) || code[1] != 1) {
        fail(m, "Invalid Hol V1 bytecode header");
        return m;
    }
    for (size_t i = 2; i < 8; ++i) {
        if (code[i] < 0 || (uint64_t) code[i] > SIZE_MAX) {
            fail(m, "Invalid Hol V1 bytecode count");
            return m;
        }
    }
    m->term_count = (size_t) code[2];
    m->instruction_count = (size_t) code[3];
    m->clause_count = (size_t) code[4];
    m->query_slots = (size_t) code[5];
    m->symbol_count = (size_t) code[7];
    size_t remaining = length - 8;
    if (m->term_count > remaining / 3) {
        fail(m, "Truncated Hol V1 term table");
        return m;
    }
    remaining -= m->term_count * 3;
    if (m->instruction_count > remaining / 4) {
        fail(m, "Truncated Hol V1 instruction table");
        return m;
    }
    remaining -= m->instruction_count * 4;
    if (m->clause_count > remaining / 4 || remaining != m->clause_count * 4 || !index_in(code[6], m->instruction_count)) {
        fail(m, "Invalid Hol V1 clause table or query entry");
        return m;
    }
    m->terms = allocate(m, m->term_count, sizeof(*m->terms));
    m->instructions = allocate(m, m->instruction_count, sizeof(*m->instructions));
    m->clauses = allocate(m, m->clause_count, sizeof(*m->clauses));
    if (m->error[0]) {
        return m;
    }
    const int64_t *words = code + 8;
    for (size_t i = 0; i < m->term_count; ++i, words += 3) {
        Template *term = &m->terms[i];
        if (words[0] == TERM_VAR && words[1] >= 0 && (uint64_t) words[1] < SIZE_MAX && words[2] == 0) {
            term->tag = TERM_VAR;
            term->a = (size_t) words[1];
            term->slots = term->a + 1;
        } else if (words[0] == TERM_CONST && index_in(words[1], m->symbol_count) && words[2] == 0) {
            term->tag = TERM_CONST;
            term->a = (size_t) words[1];
        } else if (words[0] == TERM_APP && index_in(words[1], i) && index_in(words[2], i)) {
            term->tag = TERM_APP;
            term->a = (size_t) words[1];
            term->b = (size_t) words[2];
            term->slots = m->terms[term->a].slots > m->terms[term->b].slots ? m->terms[term->a].slots : m->terms[term->b].slots;
        } else {
            fail(m, "Invalid Hol V1 term template");
            return m;
        }
    }
    for (size_t i = 0; i < m->instruction_count; ++i, words += 4) {
        int valid = 0;
        switch (words[0]) {
            case OP_RETURN:
            case OP_FAIL:
                valid = words[1] == 0 && words[2] == 0 && words[3] == 0;
                break;
            case OP_CALL:
                valid = index_in(words[1], m->term_count) && index_in(words[2], m->instruction_count) && words[3] == 0;
                break;
            case OP_UNIFY:
                valid = index_in(words[1], m->term_count) && index_in(words[2], m->term_count) && index_in(words[3], m->instruction_count);
                break;
            case OP_CHOICE:
                valid = index_in(words[1], m->instruction_count) && index_in(words[2], m->instruction_count) && words[3] == 0;
                break;
            case OP_CUT:
                valid = index_in(words[1], m->instruction_count) && words[2] == 0 && words[3] == 0;
                break;
            default:
                break;
        }
        if (!valid) {
            fail(m, "Invalid Hol V1 instruction");
            return m;
        }
        m->instructions[i] = (Instruction) { (size_t) words[1], (size_t) words[2], (size_t) words[3], (int) words[0] };
    }
    m->predicate_capacity = 8;
    if (m->clause_count > SIZE_MAX / 2) {
        fail(m, "VM predicate index size overflow");
        return m;
    }
    while (m->predicate_capacity < m->clause_count * 2) {
        if (m->predicate_capacity > SIZE_MAX / 2) {
            fail(m, "VM predicate index size overflow");
            return m;
        }
        m->predicate_capacity *= 2;
    }
    m->predicates = allocate(m, m->predicate_capacity, sizeof(*m->predicates));
    if (m->error[0]) {
        return m;
    }
    for (size_t i = 0; i < m->predicate_capacity; ++i) {
        m->predicates[i] = (Predicate) { NONE, NONE };
    }
    for (size_t i = 0; i < m->clause_count; ++i, words += 4) {
        if (!index_in(words[0], m->symbol_count) || words[1] < 0 || (uint64_t) words[1] > SIZE_MAX || !index_in(words[2], m->term_count) || !index_in(words[3], m->instruction_count)) {
            fail(m, "Invalid Hol V1 clause");
            return m;
        }
        Clause clause = { (size_t) words[0], (size_t) words[1], (size_t) words[2], (size_t) words[3], NONE };
        size_t head = clause.head;
        while (m->terms[head].tag == TERM_APP) {
            head = m->terms[head].a;
        }
        if (m->terms[head].tag != TERM_CONST || m->terms[head].a != clause.symbol || m->terms[clause.head].slots > clause.slots) {
            fail(m, "Invalid Hol V1 clause head");
            return m;
        }
        m->clauses[i] = clause;
    }
    for (size_t i = m->clause_count; i > 0; --i) {
        Clause *clause = &m->clauses[i - 1];
        Predicate *predicate = &m->predicates[predicate_bucket(m, clause->symbol)];
        clause->next = predicate->first;
        predicate->symbol = clause->symbol;
        predicate->first = i - 1;
    }
    size_t *visited = allocate(m, m->instruction_count, sizeof(*visited));
    if (!visited) {
        return m;
    }
    int valid = validate_context(m, (size_t) code[6], m->query_slots, visited, 1);
    for (size_t i = 0; valid && i < m->clause_count; ++i) {
        valid = validate_context(m, m->clauses[i].entry, m->clauses[i].slots, visited, i + 2);
    }
    free(visited);
    if (!valid) {
        return m;
    }
    size_t query_env;
    if (!new_environment(m, m->query_slots, &query_env, 1)) {
        return m;
    }
    for (size_t i = 0; i < m->term_count; ++i) {
        if (m->terms[i].tag == TERM_CONST && !push_node(m, TERM_CONST, m->terms[i].a, 0, &m->terms[i].constant)) {
            return m;
        }
    }
    m->state = (State) { (size_t) code[6], query_env, m->query_slots, 0, NONE };
    return m;
}

int hol_v1_next(HolV1Machine *m)
{
    if (!m || m->error[0]) {
        return -1;
    }
    if (m->exhausted) {
        return 0;
    }
    m->answer_ready = 0;
    if (m->resume) {
        m->resume = 0;
        if (!backtrack(m)) {
            m->exhausted = 1;
            return m->error[0] ? -1 : 0;
        }
    }
    for (size_t steps = 0; steps < 32768; ++steps) {
        Instruction instruction = m->instructions[m->state.pc];
        int success = 1;
        switch (instruction.op) {
            case OP_RETURN:
                if (m->state.continuation == NONE) {
                    if (!serialize_answer(m)) {
                        return -1;
                    }
                    m->resume = 1;
                    return 1;
                }
                m->state = m->work[m->state.continuation];
                break;
            case OP_FAIL:
                success = 0;
                break;
            case OP_CALL:
                success = call(m, instruction);
                break;
            case OP_UNIFY: {
                size_t left, right;
                success = instantiate(m, instruction.a, m->state.env, m->state.slots, &left)
                    && instantiate(m, instruction.b, m->state.env, m->state.slots, &right)
                    && unify(m, left, right);
                m->state.pc = instruction.c;
                break;
            }
            case OP_CHOICE: {
                Choice choice = { 0 };
                choice.kind = CHOICE_CODE;
                choice.checkpoint = checkpoint(m);
                choice.state = m->state;
                choice.state.pc = instruction.b;
                success = push_choice(m, choice);
                m->state.pc = instruction.a;
                break;
            }
            case OP_CUT:
                if (m->state.barrier > m->choice_count) {
                    fail(m, "Invalid VM cut barrier");
                    return -1;
                }
                m->choice_count = m->state.barrier;
                m->state.pc = instruction.a;
                break;
            default:
                fail(m, "Invalid VM instruction pointer");
                return -1;
        }
        if (!success) {
            if (m->error[0]) {
                return -1;
            }
            if (!backtrack(m)) {
                m->exhausted = 1;
                return m->error[0] ? -1 : 0;
            }
        }
    }
    return 2;
}

size_t hol_v1_answer_size(const HolV1Machine *m)
{
    return m && m->answer_ready ? m->answer_count : 0;
}

int hol_v1_answer(HolV1Machine *m, int64_t *output, size_t capacity)
{
    if (!m || m->error[0]) {
        return -1;
    }
    if (!m->answer_ready || capacity < m->answer_count || (m->answer_count && !output)) {
        fail(m, "Invalid VM answer buffer or unavailable answer");
        return -1;
    }
    if (m->answer_count) {
        memcpy(output, m->answer, m->answer_count * sizeof(*output));
    }
    return 1;
}

const char *hol_v1_error(const HolV1Machine *m)
{
    return m ? m->error : "VM allocation failed";
}

void hol_v1_destroy(HolV1Machine *m)
{
    if (!m) {
        return;
    }
    free(m->terms);
    free(m->instructions);
    free(m->clauses);
    free(m->predicates);
    free(m->heap);
    free(m->env);
    free(m->trail);
    free(m->scratch);
    free(m->work);
    free(m->choices);
    free(m->build);
    free(m->pairs);
    free(m->matches);
    free(m->answer);
    free(m);
}

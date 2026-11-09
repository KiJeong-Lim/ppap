#include "higher_machine.h"
#include "term.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

#define NONE SIZE_MAX
#define MAGIC INT64_C(0x484f4c31)

typedef struct {
    HTerm goal;
    size_t next, scope, hyps, barrier;
    uint64_t premises, call;
} Frame;

typedef struct { HTerm fact; size_t next; } Hypothesis;
typedef struct { int64_t symbol; HTerm fact; } Fact;
typedef struct { uint64_t target; int64_t *wire; size_t length; } Assignment;
typedef struct {
    HTCheckpoint terms;
    size_t work, hyps;
    uint64_t host;
} Checkpoint;
typedef struct {
    HTerm goal, head;
    size_t arity, global, local, barrier;
    Frame frame;
    int phase, fallback, equality;
} Search;
typedef struct {
    int kind;
    Checkpoint checkpoint;
    size_t work_head;
    Search search;
} Choice;

enum { ACTION_NEXT, ACTION_EXECUTE, ACTION_FAIL, ACTION_ANSWER };
enum { CONTINUE_WORK, CONTINUE_IMPLY, CONTINUE_EQUALITY, CONTINUE_DEBUG, CONTINUE_ANSWER };
enum { SEARCH_GLOBAL, SEARCH_LOCAL, SEARCH_EQUAL_LOCAL, SEARCH_EQUAL_GLOBAL };

struct HolV2Machine {
    HolTermStore *terms;
    int64_t *roles;
    size_t symbol_count, meta_count;
    Fact *facts;
    size_t fact_count;
    HTerm *query;
    size_t query_count;
    Frame *work;
    size_t work_count, work_capacity, work_head;
    Hypothesis *hyps;
    size_t hyp_count, hyp_capacity;
    Choice *choices;
    size_t choice_count, choice_capacity;
    Assignment *assignments;
    size_t assignment_count, assignment_capacity;
    Frame current;
    uint64_t host_state, next_call, origin;
    int action, debugging, assignment_failed, exhausted, answer_ready, resume_answer, end_debugged;
    int event_kind, event_continuation, event_aux;
    HTerm event_term;
    int64_t *buffer;
    size_t buffer_count, buffer_capacity;
    const char *api_error;
    char error[192];
};

static int fail(HolV2Machine *m, const char *message)
{
    if (!m->error[0]) {
        size_t n = strlen(message);
        if (n >= sizeof(m->error)) n = sizeof(m->error) - 1;
        memcpy(m->error, message, n);
        m->error[n] = '\0';
    }
    return 0;
}

static int term_ok(HolV2Machine *m, HTerm term)
{
    return term != HT_NONE || fail(m, ht_error(m->terms));
}

static int reserve(HolV2Machine *m, void **data, size_t *capacity, size_t count, size_t width)
{
    if (count <= *capacity) return 1;
    if (count > SIZE_MAX / width) return fail(m, "V2 arena size overflow");
    size_t next = *capacity ? *capacity : 32;
    while (next < count) {
        if (next > SIZE_MAX / 2) { next = count; break; }
        next *= 2;
    }
    if (next > SIZE_MAX / width) next = count;
    void *grown = realloc(*data, next * width);
    if (!grown) return fail(m, "V2 arena allocation failed");
    *data = grown;
    *capacity = next;
    return 1;
}

#define RESERVE(m,field,count) reserve((m), (void **) &(m)->field, &(m)->field##_capacity, (count), sizeof(*(m)->field))

static Checkpoint checkpoint(const HolV2Machine *m)
{
    return (Checkpoint) { ht_checkpoint(m->terms), m->work_count, m->hyp_count, m->host_state };
}

static int apply_assignments(HolV2Machine *m);

static int restore_checkpoint(HolV2Machine *m, Checkpoint saved)
{
    if (!ht_restore(m->terms, saved.terms)) return fail(m, ht_error(m->terms));
    m->work_count = saved.work;
    m->hyp_count = saved.hyps;
    m->host_state = saved.host;
    return apply_assignments(m);
}

static size_t push_frame(HolV2Machine *m, Frame frame)
{
    if (m->work_count == SIZE_MAX || !RESERVE(m, work, m->work_count + 1)) return NONE;
    size_t result = m->work_count++;
    m->work[result] = frame;
    return result;
}

static int schedule(HolV2Machine *m, HTerm goal, Frame environment, size_t next)
{
    environment.goal = goal;
    environment.next = next;
    size_t result = push_frame(m, environment);
    if (result == NONE) return 0;
    m->work_head = result;
    m->end_debugged = 0;
    m->action = ACTION_NEXT;
    return 1;
}

static int push_choice(HolV2Machine *m, Choice choice)
{
    if (m->choice_count == SIZE_MAX || !reserve(m, (void **) &m->choices, &m->choice_capacity, m->choice_count + 1, sizeof(*m->choices))) return 0;
    m->choices[m->choice_count++] = choice;
    return 1;
}

static int role(const HolV2Machine *m, HTerm head)
{
    HTView view = ht_view(m->terms, ht_deref(m->terms, head));
    return view.tag == HT_CONST && view.symbol < m->symbol_count ? (int) m->roles[view.symbol] : HV2_ORDINARY;
}

static int same_head(const HolV2Machine *m, HTerm left, HTerm right)
{
    HTView lhs = ht_view(m->terms, ht_deref(m->terms, left));
    HTView rhs = ht_view(m->terms, ht_deref(m->terms, right));
    if (lhs.tag != rhs.tag) return 0;
    if (lhs.tag == HT_CONST) return lhs.symbol == rhs.symbol;
    if (lhs.tag == HT_NOMINAL) return lhs.uid == rhs.uid;
    return 0;
}

static int event(HolV2Machine *m, int kind, HTerm term, int continuation, int auxiliary)
{
    m->event_kind = kind;
    m->event_term = term;
    m->event_continuation = continuation;
    m->event_aux = auxiliary;
    return 1;
}

static HTerm true_term(HolV2Machine *m)
{
    for (size_t i = 0; i < m->symbol_count; ++i) {
        if (m->roles[i] == HV2_TRUE) return ht_constant(m->terms, i, -1);
    }
    fail(m, "V2 symbol table has no true operator");
    return HT_NONE;
}

static int normalized_spine(HolV2Machine *m, HTerm term, HTSpine *spine)
{
    HTerm normalized = ht_normalize(m->terms, term, HT_HNF);
    return normalized != HT_NONE && ht_spine(m->terms, normalized, spine);
}

static int instantiate_fact(HolV2Machine *m, HTerm fact, size_t scope, HTerm *head, HTerm *body)
{
    for (;;) {
        HTSpine spine;
        if (!normalized_spine(m, fact, &spine)) return fail(m, ht_error(m->terms));
        int operation = role(m, spine.head);
        if ((operation == HV2_PI || operation == HV2_TY_PI) && spine.count == 1) {
            HTerm function = spine.args[0];
            HTView view = ht_view(m->terms, ht_deref(m->terms, function));
            int64_t meta = view.tag == HT_LAM ? view.meta : -1;
            HTerm variable = ht_var(m->terms, scope, operation == HV2_TY_PI, meta);
            ht_spine_free(&spine);
            if (!term_ok(m, variable)) return 0;
            fact = ht_apply(m->terms, function, variable);
            if (!term_ok(m, fact)) return 0;
        } else {
            if (operation == HV2_IF && spine.count == 2) {
                *head = spine.args[0];
                *body = spine.args[1];
            } else {
                *head = fact;
                *body = true_term(m);
            }
            ht_spine_free(&spine);
            return term_ok(m, *body);
        }
    }
}

static int try_search(HolV2Machine *m, Search search, Checkpoint saved)
{
    for (;;) {
        if (!restore_checkpoint(m, saved)) return 0;
        HTerm fact = HT_NONE;
        if (search.phase == SEARCH_GLOBAL || search.phase == SEARCH_EQUAL_GLOBAL) {
            HTView head = ht_view(m->terms, ht_deref(m->terms, search.head));
            while (search.global < m->fact_count) {
                Fact candidate = m->facts[search.global++];
                if (candidate.symbol < 0 || (head.tag == HT_CONST && (uint64_t) candidate.symbol == head.symbol)) {
                    fact = candidate.fact;
                    break;
                }
            }
            if (fact == HT_NONE) {
                if (search.phase == SEARCH_EQUAL_GLOBAL) return 0;
                search.phase = SEARCH_LOCAL;
                continue;
            }
        } else {
            if (search.local != NONE) {
                Hypothesis candidate = m->hyps[search.local];
                search.local = candidate.next;
                fact = candidate.fact;
            } else if (search.phase == SEARCH_EQUAL_LOCAL && search.fallback) {
                if (search.equality == 2) {
                    m->work_head = search.frame.next;
                    m->action = ACTION_NEXT;
                    return 1;
                }
                if (search.equality == 3) return 0;
                search.phase = SEARCH_EQUAL_GLOBAL;
                continue;
            } else {
                return 0;
            }
        }
        HTerm head, body;
        if (!instantiate_fact(m, fact, search.frame.scope, &head, &body)) return 0;
        HTSpine spine;
        if (!normalized_spine(m, head, &spine)) return fail(m, ht_error(m->terms));
        int matches = same_head(m, search.head, spine.head);
        size_t arity = spine.count;
        ht_spine_free(&spine);
        if (!matches) continue;
        if (arity != search.arity) return fail(m, "V2 clause head has inconsistent arity");
        int unified = ht_unify(m->terms, search.goal, head);
        if (unified < 0) return fail(m, ht_error(m->terms));
        if (!unified) continue;
        Search alternative = search;
        if (alternative.phase == SEARCH_EQUAL_LOCAL) alternative.fallback = 0;
        Choice choice = { 0 };
        choice.kind = 1;
        choice.checkpoint = saved;
        choice.search = alternative;
        if (!push_choice(m, choice)) return 0;
        Frame environment = search.frame;
        environment.barrier = search.barrier;
        if (!schedule(m, body, environment, environment.next)) return 0;
        m->current = environment;
        if (m->host_state) event(m, HV2_EVENT_SETTLE, HT_NONE, CONTINUE_WORK, 0);
        return 1;
    }
}

static int begin_search(HolV2Machine *m, int equality)
{
    HTSpine spine;
    if (!normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    HTView view = ht_view(m->terms, ht_deref(m->terms, spine.head));
    if (view.tag != HT_CONST && view.tag != HT_NOMINAL) {
        ht_spine_free(&spine);
        return fail(m, "Bad V2 goal: predicate head is not rigid");
    }
    if (m->next_call >= INT64_MAX) {
        ht_spine_free(&spine);
        return fail(m, "V2 call identity exhausted");
    }
    Search search = { 0 };
    search.goal = m->current.goal;
    search.head = spine.head;
    search.arity = spine.count;
    search.local = m->current.hyps;
    search.barrier = m->choice_count;
    search.frame = m->current;
    search.frame.call = m->next_call++;
    search.phase = equality ? SEARCH_EQUAL_LOCAL : SEARCH_GLOBAL;
    search.fallback = equality != 0;
    search.equality = equality;
    ht_spine_free(&spine);
    return try_search(m, search, checkpoint(m));
}

static int backtrack(HolV2Machine *m)
{
    m->event_kind = 0;
    m->end_debugged = 0;
    while (m->choice_count) {
        Choice choice = m->choices[--m->choice_count];
        if (!restore_checkpoint(m, choice.checkpoint)) {
            if (m->error[0]) return 0;
            continue;
        }
        if (choice.kind == 0) {
            m->work_head = choice.work_head;
            m->action = ACTION_NEXT;
            return 1;
        }
        if (try_search(m, choice.search, choice.checkpoint)) return 1;
        if (m->error[0]) return 0;
    }
    m->exhausted = 1;
    return 0;
}

/* Expand under binders and multi-head conclusions without freshening captures. */
static int expand_assumption(HolV2Machine *m, HTerm fact, HTerm **out, size_t *count, size_t *capacity)
{
    HTSpine spine;
    if (!normalized_spine(m, fact, &spine)) return fail(m, ht_error(m->terms));
    int operation = role(m, spine.head);
    int success = 1;
    if (operation == HV2_AND && spine.count == 2) {
        success = expand_assumption(m, spine.args[0], out, count, capacity)
            && expand_assumption(m, spine.args[1], out, count, capacity);
    } else if (operation == HV2_IF && spine.count == 2) {
        size_t start = *count;
        success = expand_assumption(m, spine.args[0], out, count, capacity);
        for (size_t i = start; success && i < *count; ++i) {
            HTerm partial = ht_app(m->terms, spine.head, (*out)[i], -1);
            HTerm expanded = ht_app(m->terms, partial, spine.args[1], -1);
            success = term_ok(m, partial) && term_ok(m, expanded);
            (*out)[i] = expanded;
        }
    } else if ((operation == HV2_PI || operation == HV2_TY_PI) && spine.count == 1) {
        HTView lambda = ht_view(m->terms, ht_deref(m->terms, spine.args[0]));
        if (lambda.tag == HT_LAM) {
            size_t start = *count;
            success = expand_assumption(m, lambda.a, out, count, capacity);
            for (size_t i = start; success && i < *count; ++i) {
                HTerm binder = ht_lam(m->terms, (*out)[i], lambda.meta);
                HTerm expanded = ht_app(m->terms, spine.head, binder, -1);
                success = term_ok(m, binder) && term_ok(m, expanded);
                (*out)[i] = expanded;
            }
        } else {
            success = reserve(m, (void **) out, capacity, *count + 1, sizeof(**out));
            if (success) (*out)[(*count)++] = fact;
        }
    } else {
        success = reserve(m, (void **) out, capacity, *count + 1, sizeof(**out));
        if (success) (*out)[(*count)++] = fact;
    }
    ht_spine_free(&spine);
    return success;
}

static int enter_implication(HolV2Machine *m, uint64_t premises)
{
    HTSpine spine;
    if (!normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    if (spine.count != 2) { ht_spine_free(&spine); return fail(m, "Malformed V2 implication"); }
    HTerm *expanded = NULL;
    size_t count = 0, capacity = 0;
    int success = expand_assumption(m, spine.args[0], &expanded, &count, &capacity);
    size_t hyps = m->current.hyps;
    for (size_t i = count; success && i > 0; --i) {
        success = reserve(m, (void **) &m->hyps, &m->hyp_capacity, m->hyp_count + 1, sizeof(*m->hyps));
        if (success) {
            m->hyps[m->hyp_count] = (Hypothesis) { expanded[i - 1], hyps };
            hyps = m->hyp_count++;
        }
    }
    if (success) {
        Frame inside = m->current;
        inside.hyps = hyps;
        inside.premises = premises;
        success = schedule(m, spine.args[1], inside, m->current.next);
    }
    free(expanded);
    ht_spine_free(&spine);
    return success;
}

static int execute_current(HolV2Machine *m)
{
    HTSpine spine;
    if (!normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    int operation = role(m, spine.head);
    size_t arity = spine.count;
    int success = 1;
    m->action = ACTION_NEXT;
    switch (operation) {
        case HV2_TRUE:
            if (arity) success = fail(m, "Malformed V2 true goal");
            break;
        case HV2_FAIL:
            if (arity) fail(m, "Malformed V2 fail goal");
            success = 0;
            break;
        case HV2_CUT:
            if (arity || m->current.barrier > m->choice_count) success = fail(m, "Invalid V2 cut activation");
            else m->choice_count = m->current.barrier;
            break;
        case HV2_AND:
            if (arity != 2) success = fail(m, "Malformed V2 conjunction");
            else {
                Frame right = m->current;
                right.goal = spine.args[1];
                right.next = m->current.next;
                size_t continuation = push_frame(m, right);
                success = continuation != NONE && schedule(m, spine.args[0], m->current, continuation);
            }
            break;
        case HV2_OR:
            if (arity != 2) success = fail(m, "Malformed V2 disjunction");
            else {
                Frame right = m->current;
                right.goal = spine.args[1];
                right.next = m->current.next;
                size_t alternative = push_frame(m, right);
                Choice choice = { 0 };
                choice.kind = 0;
                choice.checkpoint = checkpoint(m);
                choice.work_head = alternative;
                success = alternative != NONE && push_choice(m, choice) && schedule(m, spine.args[0], m->current, m->current.next);
            }
            break;
        case HV2_PI:
        case HV2_SIGMA:
            if (arity != 1 || (operation == HV2_PI && m->current.scope == SIZE_MAX)) success = fail(m, "Malformed V2 quantifier");
            else {
                HTView function = ht_view(m->terms, ht_deref(m->terms, spine.args[0]));
                int64_t meta = function.tag == HT_LAM ? function.meta : -1;
                size_t scope = m->current.scope + (operation == HV2_PI);
                HTerm binder = operation == HV2_PI ? ht_nominal(m->terms, scope, meta) : ht_var(m->terms, scope, 0, meta);
                HTerm goal = ht_apply(m->terms, spine.args[0], binder);
                Frame inside = m->current;
                inside.scope = scope;
                success = term_ok(m, binder) && term_ok(m, goal) && schedule(m, goal, inside, m->current.next);
            }
            break;
        case HV2_IMPLY:
            if (arity != 2) success = fail(m, "Malformed V2 implication");
            else success = event(m, HV2_EVENT_IMPLY, spine.args[0], CONTINUE_IMPLY, 0);
            break;
        case HV2_EQ:
            if (arity != 3) success = fail(m, "Malformed V2 equality");
            else success = event(m, HV2_EVENT_EQUALITY, m->current.goal, CONTINUE_EQUALITY, 0);
            break;
        case HV2_IS:
        case HV2_LE:
        case HV2_LT:
        case HV2_GE:
        case HV2_GT:
        case HV2_READ:
        case HV2_PRINT:
        case HV2_DEBUG:
        case HV2_PRESBURGER:
            success = event(m, HV2_EVENT_PRIMITIVE, m->current.goal, CONTINUE_WORK, 0);
            break;
        case HV2_TY_PI:
        case HV2_IF:
            success = fail(m, "A V2 clause operator appeared as a goal");
            break;
        default:
            success = begin_search(m, 0);
            break;
    }
    ht_spine_free(&spine);
    return success;
}

static int valid_index(int64_t index, size_t limit)
{
    return index >= 0 && (uint64_t) index < limit;
}

static int valid_meta(int64_t meta, size_t count)
{
    return meta == -1 || valid_index(meta, count);
}

static void *copy_array(const void *source, size_t count, size_t width)
{
    if (!count) return NULL;
    if (count > SIZE_MAX / width) return NULL;
    void *copy = malloc(count * width);
    if (copy) memcpy(copy, source, count * width);
    return copy;
}

HolV2Machine *hol_v2_create(const int64_t *code, size_t length)
{
    static _Atomic uint64_t next_origin = 1;
    HolV2Machine *m = calloc(1, sizeof(*m));
    if (!m) return NULL;
    m->work_head = NONE;
    m->next_call = 1;
    m->origin = atomic_fetch_add(&next_origin, 1);
    if (!m->origin) { fail(m, "V2 runtime identity exhausted"); return m; }
    m->terms = ht_create();
    if (!m->terms) { fail(m, "V2 term store allocation failed"); return m; }
    if (!code || length < 8 || code[0] != MAGIC || code[1] != 2) {
        fail(m, "Invalid V2 wordcode header");
        return m;
    }
    for (size_t i = 2; i < 8; ++i) {
        if (code[i] < 0 || (uint64_t) code[i] > SIZE_MAX) {
            fail(m, "Invalid V2 wordcode count");
            return m;
        }
    }
    size_t term_count = (size_t) code[2];
    m->symbol_count = (size_t) code[3];
    m->fact_count = (size_t) code[4];
    m->query_count = (size_t) code[5];
    m->meta_count = (size_t) code[7];
    size_t remaining = length - 8;
    if (m->query_count > remaining / 2) { fail(m, "Truncated V2 query table"); return m; }
    const int64_t *queries = code + 8;
    remaining -= 2 * m->query_count;
    if (m->symbol_count > remaining) { fail(m, "Truncated V2 symbol table"); return m; }
    const int64_t *roles = queries + 2 * m->query_count;
    remaining -= m->symbol_count;
    if (term_count > remaining / 6) { fail(m, "Truncated V2 template table"); return m; }
    const int64_t *templates = roles + m->symbol_count;
    remaining -= term_count * 6;
    if (m->fact_count > remaining / 2) { fail(m, "Truncated V2 clause table"); return m; }
    const int64_t *facts = templates + term_count * 6;
    remaining -= m->fact_count * 2;
    const int64_t *digits = facts + m->fact_count * 2;
    if (!valid_index(code[6], term_count)) { fail(m, "Invalid V2 query root"); return m; }
    m->roles = copy_array(roles, m->symbol_count, sizeof(*m->roles));
    if (m->symbol_count && !m->roles) { fail(m, "V2 symbol allocation failed"); return m; }
    int has_true = 0, has_successor = 0;
    for (size_t i = 0; i < m->symbol_count; ++i) {
        if (roles[i] < HV2_ORDINARY || roles[i] > HV2_SUCCESSOR) { fail(m, "Invalid V2 symbol role"); return m; }
        if (roles[i] == HV2_TRUE) has_true = 1;
        if (roles[i] == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, i)) { fail(m, ht_error(m->terms)); return m; }
        if (roles[i] == HV2_SUCCESSOR) { ht_set_successor(m->terms, i); has_successor = 1; }
    }
    if (!has_true || !has_successor) { fail(m, "V2 requires true and successor symbols"); return m; }
    if (m->query_count > SIZE_MAX / sizeof(*m->query)) { fail(m, "V2 query allocation overflow"); return m; }
    m->query = m->query_count ? calloc(m->query_count, sizeof(*m->query)) : NULL;
    if (m->query_count && !m->query) { fail(m, "V2 query allocation failed"); return m; }
    for (size_t i = 0; i < m->query_count; ++i) {
        if ((queries[2 * i] != 0 && queries[2 * i] != 1) || !valid_meta(queries[2 * i + 1], m->meta_count)) {
            fail(m, "Invalid V2 query descriptor");
            return m;
        }
        m->query[i] = ht_var(m->terms, 0, (int) queries[2 * i], queries[2 * i + 1]);
        if (!term_ok(m, m->query[i])) return m;
    }
    HTerm *roots = term_count <= SIZE_MAX / sizeof(*roots) ? malloc(term_count * sizeof(*roots)) : NULL;
    if (!roots) { fail(m, "V2 template allocation failed"); return m; }
    for (size_t i = 0; i < term_count; ++i) {
        const int64_t *row = templates + 6 * i;
        HTerm value = HT_NONE;
        if (row[3] || row[4] || !valid_meta(row[5], m->meta_count)) {
            fail(m, "Invalid V2 template metadata or reserved operand");
            break;
        }
        switch (row[0]) {
            case 0:
                if (valid_index(row[1], m->query_count) && row[2] == 0) value = m->query[row[1]];
                break;
            case 1:
                if (valid_index(row[1], m->symbol_count) && row[2] == 0) value = ht_constant(m->terms, (size_t) row[1], row[5]);
                break;
            case 2:
                if (valid_index(row[1], i) && valid_index(row[2], i)) value = ht_app(m->terms, roots[row[1]], roots[row[2]], row[5]);
                break;
            case 3:
                if (row[1] >= 0 && (uint64_t) row[1] <= SIZE_MAX && row[2] == 0) value = ht_index(m->terms, (size_t) row[1]);
                break;
            case 4:
                if (valid_index(row[1], i) && row[2] == 0) value = ht_lam(m->terms, roots[row[1]], row[5]);
                break;
            case 5:
                if (row[1] >= 0 && row[2] > 0 && (uint64_t) row[1] <= remaining && (uint64_t) row[2] <= remaining - (size_t) row[1]) {
                    size_t n = (size_t) row[2];
                    char *text = n < SIZE_MAX ? malloc(n + 1) : NULL;
                    if (!text) { fail(m, "V2 natural allocation failed"); break; }
                    int valid = 1;
                    for (size_t j = 0; j < n; ++j) {
                        int64_t ch = digits[(size_t) row[1] + j];
                        if (ch < '0' || ch > '9') valid = 0;
                        text[j] = (char) ch;
                    }
                    text[n] = '\0';
                    if (valid && (n == 1 || text[0] != '0')) value = ht_nat(m->terms, text);
                    free(text);
                }
                break;
            case 6:
                if (!row[1] && !row[2]) value = ht_wildcard(m->terms);
                break;
            default:
                break;
        }
        if (value == HT_NONE) {
            const char *message = ht_error(m->terms);
            fail(m, message && message[0] ? message : "Invalid V2 term template");
            break;
        }
        roots[i] = value;
    }
    if (!m->error[0]) {
        if (m->fact_count > SIZE_MAX / sizeof(*m->facts)) fail(m, "V2 fact allocation overflow");
        else {
            m->facts = m->fact_count ? calloc(m->fact_count, sizeof(*m->facts)) : NULL;
            if (m->fact_count && !m->facts) fail(m, "V2 fact allocation failed");
        }
    }
    for (size_t i = 0; !m->error[0] && i < m->fact_count; ++i) {
        int64_t symbol = facts[2 * i], root = facts[2 * i + 1];
        if ((symbol != -1 && !valid_index(symbol, m->symbol_count)) || !valid_index(root, term_count)) fail(m, "Invalid V2 fact descriptor");
        else m->facts[i] = (Fact) { symbol, roots[root] };
    }
    if (!m->error[0]) {
        Frame initial = { roots[code[6]], NONE, 0, NONE, 0, 0, 0 };
        m->work_head = push_frame(m, initial);
    }
    free(roots);
    return m;
}

int hol_v2_next(HolV2Machine *m)
{
    if (!m || m->error[0]) return -1;
    m->api_error = NULL;
    if (m->assignment_failed && !m->event_kind) { m->assignment_failed = 0; m->action = ACTION_FAIL; }
    if (m->event_kind) return 3;
    if (m->exhausted) return 0;
    m->answer_ready = 0;
    if (m->resume_answer) {
        m->resume_answer = 0;
        m->action = ACTION_FAIL;
    }
    for (size_t budget = 0; budget < 4096; ++budget) {
        if (m->action == ACTION_FAIL) {
            if (!backtrack(m)) return m->error[0] ? -1 : 0;
            if (m->event_kind) return 3;
        }
        if (m->action == ACTION_ANSWER) {
            m->answer_ready = 1;
            m->resume_answer = 1;
            m->action = ACTION_NEXT;
            return 1;
        }
        if (m->action == ACTION_EXECUTE) {
            if (!execute_current(m)) {
                if (m->error[0]) return -1;
                m->action = ACTION_FAIL;
            }
            if (m->event_kind) return 3;
            continue;
        }
        if (m->work_head == NONE) {
            if (m->debugging && !m->end_debugged) {
                m->end_debugged = 1;
                event(m, HV2_EVENT_DEBUG, HT_NONE, CONTINUE_WORK, 1);
                return 3;
            }
            int okay = ht_retry(m->terms);
            if (okay < 0) { fail(m, ht_error(m->terms)); return -1; }
            if (!okay) { m->action = ACTION_FAIL; continue; }
            if (m->host_state) {
                event(m, HV2_EVENT_SETTLE, HT_NONE, CONTINUE_ANSWER, 1);
                return 3;
            }
            m->action = ACTION_ANSWER;
            continue;
        }
        m->current = m->work[m->work_head];
        m->end_debugged = 0;
        m->work_head = m->current.next;
        m->action = ACTION_EXECUTE;
        if (m->debugging) {
            event(m, HV2_EVENT_DEBUG, m->current.goal, CONTINUE_DEBUG, 0);
            return 3;
        }
    }
    return 2;
}

static int push_word(HolV2Machine *m, int64_t word)
{
    if (m->buffer_count == SIZE_MAX || !reserve(m, (void **) &m->buffer, &m->buffer_capacity, m->buffer_count + 1, sizeof(*m->buffer))) return 0;
    m->buffer[m->buffer_count++] = word;
    return 1;
}

static int push_term(HolV2Machine *m, HTerm term)
{
    int64_t *wire = NULL;
    size_t length = 0;
    if (!ht_export(m->terms, term, &wire, &length)) return fail(m, ht_error(m->terms));
    int success = length <= SIZE_MAX - m->buffer_count
        && reserve(m, (void **) &m->buffer, &m->buffer_capacity, m->buffer_count + length, sizeof(*m->buffer));
    if (success) {
        memcpy(m->buffer + m->buffer_count, wire, length * sizeof(*wire));
        m->buffer_count += length;
    } else if (!m->error[0]) fail(m, "V2 export size overflow");
    free(wire);
    return success;
}

static int copy_buffer(HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || m->error[0]) return -1;
    if (capacity < m->buffer_count || (m->buffer_count && !output)) { fail(m, "Invalid V2 output buffer"); return -1; }
    if (m->buffer_count) memcpy(output, m->buffer, m->buffer_count * sizeof(*output));
    return 1;
}

size_t hol_v2_answer_size(HolV2Machine *m)
{
    if (!m || m->error[0] || !m->answer_ready) return 0;
    m->buffer_count = 0;
    if (!push_word(m, (int64_t) m->query_count)) return 0;
    for (size_t i = 0; i < m->query_count; ++i) if (!push_term(m, m->query[i])) return 0;
    return m->buffer_count;
}

int hol_v2_answer(HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || !m->answer_ready) return -1;
    return copy_buffer(m, output, capacity);
}

size_t hol_v2_state_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    size_t heap = ht_heap_count(m->terms), variables = 0;
    for (size_t i = 0; i < heap; ++i) if (ht_view(m->terms, i).tag == HT_VAR) ++variables;
    if (!push_word(m, (int64_t) variables)) return 0;
    for (size_t i = 0; i < heap; ++i) {
        HTView variable = ht_view(m->terms, i);
        if (variable.tag != HT_VAR) continue;
        if (!push_word(m, HT_VAR) || !push_word(m, (int64_t) variable.uid)
            || !push_word(m, (int64_t) variable.scope) || !push_word(m, variable.is_type)
            || !push_word(m, variable.meta) || !push_term(m, i)) return 0;
    }
    size_t pending = ht_pending_count(m->terms);
    if (!push_word(m, (int64_t) pending)) return 0;
    for (size_t i = 0; i < pending; ++i) {
        HTerm left, right;
        if (!ht_pending(m->terms, i, &left, &right) || !push_term(m, left) || !push_term(m, right)) return 0;
    }
    return m->buffer_count;
}

int hol_v2_state(HolV2Machine *m, int64_t *output, size_t capacity)
{
    return copy_buffer(m, output, capacity);
}

size_t hol_v2_event_size(HolV2Machine *m)
{
    if (!m || m->error[0] || !m->event_kind) return 0;
    m->buffer_count = 0;
    if (!push_word(m, m->event_term == HT_NONE ? 0 : 1)) return 0;
    if (m->event_term != HT_NONE && !push_term(m, m->event_term)) return 0;
    return m->buffer_count;
}

int hol_v2_event(HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || !m->event_kind) return -1;
    return copy_buffer(m, output, capacity);
}

int hol_v2_event_info(const HolV2Machine *m, int64_t *output, size_t capacity)
{
    if (!m || !m->event_kind || !output || capacity < 6) return -1;
    output[0] = m->event_kind;
    output[1] = (int64_t) m->host_state;
    output[2] = (int64_t) m->current.premises;
    output[3] = (int64_t) m->current.scope;
    output[4] = (int64_t) m->current.call;
    output[5] = m->event_aux;
    return 1;
}

uint64_t hol_v2_host_state(const HolV2Machine *m)
{
    return m ? m->host_state : 0;
}

size_t hol_v2_frames_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    size_t count = m->event_kind == HV2_EVENT_DEBUG && m->event_term != HT_NONE ? 1 : 0;
    for (size_t at = m->work_head; at != NONE; at = m->work[at].next) ++count;
    if (!push_word(m, (int64_t) count)) return 0;
    Frame frame = m->current;
    size_t at = m->work_head;
    int current = m->event_kind == HV2_EVENT_DEBUG && m->event_term != HT_NONE;
    while (current || at != NONE) {
        if (current) current = 0;
        else { frame = m->work[at]; at = frame.next; }
        size_t hyps = 0;
        for (size_t h = frame.hyps; h != NONE; h = m->hyps[h].next) ++hyps;
        if (!push_word(m, (int64_t) frame.scope) || !push_word(m, (int64_t) frame.call) || !push_word(m, (int64_t) hyps)) return 0;
        for (size_t h = frame.hyps; h != NONE; h = m->hyps[h].next) if (!push_term(m, m->hyps[h].fact)) return 0;
        if (!push_term(m, frame.goal)) return 0;
    }
    return m->buffer_count;
}

int hol_v2_frames(HolV2Machine *m, int64_t *output, size_t capacity)
{
    return copy_buffer(m, output, capacity);
}

int hol_v2_resume(HolV2Machine *m, int result, uint64_t host_state, uint64_t premises, const int64_t *bindings, size_t length)
{
    if (!m || m->error[0] || !m->event_kind) return -1;
    if (result < 0 || result > 4 || host_state > INT64_MAX || premises > INT64_MAX || !bindings || !length || bindings[0] < 0) {
        fail(m, "Invalid V2 host response");
        return -1;
    }
    int continuation = m->event_continuation;
    m->event_kind = 0;
    if (m->assignment_failed) { m->assignment_failed = 0; m->action = ACTION_FAIL; return 1; }
    if (!result) { m->action = ACTION_FAIL; return 1; }
    size_t at = 1;
    uint64_t count = (uint64_t) bindings[0];
    for (uint64_t i = 0; i < count; ++i) {
        HTerm left = ht_import(m->terms, bindings, length, &at);
        HTerm right = ht_import(m->terms, bindings, length, &at);
        if (!term_ok(m, left) || !term_ok(m, right)) return -1;
        int unified = ht_unify(m->terms, left, right);
        if (unified < 0) { fail(m, ht_error(m->terms)); return -1; }
        if (!unified) { m->action = ACTION_FAIL; return 1; }
    }
    if (at != length) { fail(m, "Trailing V2 host binding words"); return -1; }
    m->host_state = host_state;
    m->action = ACTION_NEXT;
    int success = 1;
    switch (continuation) {
        case CONTINUE_IMPLY:
            success = enter_implication(m, premises);
            break;
        case CONTINUE_EQUALITY:
            success = begin_search(m, result);
            break;
        case CONTINUE_DEBUG:
            m->action = ACTION_EXECUTE;
            break;
        case CONTINUE_ANSWER:
            m->action = ACTION_ANSWER;
            break;
        default:
            break;
    }
    if (!success) {
        if (m->error[0]) return -1;
        m->action = ACTION_FAIL;
    }
    return 1;
}

void hol_v2_set_debugging(HolV2Machine *m, int enabled)
{
    if (m) m->debugging = enabled != 0;
}

int hol_v2_ensure_symbol(HolV2Machine *m, size_t symbol, int operation)
{
    if (!m || m->error[0]) return -1;
    if (operation < HV2_ORDINARY || operation > HV2_SUCCESSOR || symbol >= INT64_MAX || symbol >= SIZE_MAX / sizeof(*m->roles)) return fail(m, "Invalid V2 dynamic symbol") ? 1 : -1;
    if (symbol < m->symbol_count) {
        if (m->roles[symbol] != operation) { fail(m, "V2 dynamic symbol role conflict"); return -1; }
        if (operation == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, symbol)) { fail(m, ht_error(m->terms)); return -1; }
        return 1;
    }
    int64_t *roles = realloc(m->roles, (symbol + 1) * sizeof(*m->roles));
    if (!roles) { fail(m, "V2 dynamic symbol allocation failed"); return -1; }
    m->roles = roles;
    while (m->symbol_count <= symbol) m->roles[m->symbol_count++] = HV2_ORDINARY;
    m->roles[symbol] = operation;
    if (operation == HV2_SUCCESSOR) ht_set_successor(m->terms, symbol);
    if (operation == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, symbol)) { fail(m, ht_error(m->terms)); return -1; }
    return 1;
}

uint64_t hol_v2_reserve_uid(HolV2Machine *m)
{
    if (!m || m->error[0]) return UINT64_MAX;
    uint64_t uid = ht_next_uid(m->terms);
    if (uid >= INT64_MAX || !ht_advance_uid(m->terms, uid + 1)) { fail(m, "V2 variable identity exhausted"); return UINT64_MAX; }
    return uid;
}

static void release_fields(HolV2Machine *m)
{
    ht_destroy(m->terms);
    free(m->roles);
    free(m->facts);
    free(m->query);
    free(m->work);
    free(m->hyps);
    free(m->choices);
    free(m->buffer);
    for (size_t i = 0; i < m->assignment_count; ++i) free(m->assignments[i].wire);
    free(m->assignments);
}

void hol_v2_destroy(HolV2Machine *m)
{
    if (m) { release_fields(m); free(m); }
}

const char *hol_v2_error(const HolV2Machine *m)
{
    return m ? (m->error[0] ? m->error : m->api_error ? m->api_error : "") : "V2 allocation failed";
}

HolV2Machine *hol_v2_clone(const HolV2Machine *source)
{
    if (!source || source->error[0]) return NULL;
    HolV2Machine *copy = calloc(1, sizeof(*copy));
    if (!copy) return NULL;
    *copy = *source;
    copy->assignment_count = 0;
    copy->assignment_capacity = source->assignment_count;
    copy->assignments = source->assignment_count ? calloc(source->assignment_count, sizeof(*source->assignments)) : NULL;
    copy->terms = ht_clone(source->terms);
    copy->roles = copy_array(source->roles, source->symbol_count, sizeof(*source->roles));
    copy->facts = copy_array(source->facts, source->fact_count, sizeof(*source->facts));
    copy->query = copy_array(source->query, source->query_count, sizeof(*source->query));
    copy->work = copy_array(source->work, source->work_count, sizeof(*source->work));
    copy->hyps = copy_array(source->hyps, source->hyp_count, sizeof(*source->hyps));
    copy->choices = copy_array(source->choices, source->choice_count, sizeof(*source->choices));
    copy->buffer = copy_array(source->buffer, source->buffer_count, sizeof(*source->buffer));
    copy->work_capacity = copy->work_count;
    copy->hyp_capacity = copy->hyp_count;
    copy->choice_capacity = copy->choice_count;
    copy->buffer_capacity = copy->buffer_count;
    if (!copy->terms || (source->assignment_count && !copy->assignments) || (copy->symbol_count && !copy->roles) || (copy->fact_count && !copy->facts)
        || (copy->query_count && !copy->query) || (copy->work_count && !copy->work)
        || (copy->hyp_count && !copy->hyps) || (copy->choice_count && !copy->choices)
        || (copy->buffer_count && !copy->buffer)) {
        hol_v2_destroy(copy);
        return NULL;
    }
    for (size_t i = 0; i < source->assignment_count; ++i) {
        Assignment original = source->assignments[i];
        int64_t *wire = copy_array(original.wire, original.length, sizeof(*wire));
        if (!wire) { hol_v2_destroy(copy); return NULL; }
        copy->assignments[copy->assignment_count++] = (Assignment) { original.target, wire, original.length };
    }
    return copy;
}

int hol_v2_restore(HolV2Machine *m, const HolV2Machine *snapshot)
{
    if (!m || !snapshot) return -1;
    if (m->origin != snapshot->origin || snapshot->error[0]) {
        m->api_error = "Snapshot belongs to a different V2 runtime or contains an error";
        return -1;
    }
    m->api_error = NULL;
    HolV2Machine *restored = hol_v2_clone(snapshot);
    if (!restored) { fail(m, "V2 snapshot allocation failed"); return -1; }
    if (!ht_preserve_identity_history(restored->terms, m->terms)) {
        hol_v2_destroy(restored);
        fail(m, "V2 snapshot identity preservation failed");
        return -1;
    }
    if (m->next_call > restored->next_call) restored->next_call = m->next_call;
    for (size_t i = restored->symbol_count; i < m->symbol_count; ++i) {
        if (hol_v2_ensure_symbol(restored, i, (int) m->roles[i]) < 0) {
            hol_v2_destroy(restored);
            fail(m, "V2 snapshot symbol preservation failed");
            return -1;
        }
    }
    if (!ht_set_work_limit(restored->terms, ht_work_limit(m->terms))) {
        hol_v2_destroy(restored);
        fail(m, "V2 snapshot work-limit preservation failed");
        return -1;
    }
    int debugging = m->debugging;
    release_fields(m);
    *m = *restored;
    m->debugging = debugging;
    free(restored);
    return 1;
}

static int skip_wire(const int64_t *wire, size_t length, size_t *offset)
{
    size_t remaining = 1;
    while (remaining) {
        if (*offset >= length) return 0;
        int64_t tag = wire[(*offset)++];
        --remaining;
        size_t fields = 0, children = 0;
        switch (tag) {
            case HT_VAR: fields = 4; break;
            case HT_CONST: fields = 2; break;
            case HT_APP: fields = 1; children = 2; break;
            case HT_INDEX: fields = 1; break;
            case HT_LAM: fields = 1; children = 1; break;
            case HT_NOMINAL: fields = 3; break;
            case HT_NAT:
                if (*offset >= length || wire[*offset] <= 0 || (uint64_t) wire[*offset] > length - *offset - 1) return 0;
                fields = (size_t) wire[(*offset)++] ;
                break;
            case HT_WILD: break;
            default: return 0;
        }
        if (fields > length - *offset || children > SIZE_MAX - remaining) return 0;
        *offset += fields;
        remaining += children;
    }
    return 1;
}

static int apply_assignments(HolV2Machine *m)
{
    for (size_t i = 0; i < m->assignment_count; ++i) {
        Assignment assignment = m->assignments[i];
        HTerm target = ht_lookup_uid(m->terms, assignment.target);
        if (target == HT_NONE) continue;
        size_t at = 0;
        HTerm value = ht_import_restored(m->terms, assignment.wire, assignment.length, &at);
        if (!term_ok(m, value)) return 0;
        int unified = ht_assign_checked(m->terms, target, value);
        if (unified < 0) return fail(m, ht_error(m->terms));
        if (!unified) return 0;
    }
    return 1;
}

int hol_v2_assign(HolV2Machine *m, const int64_t *bindings, size_t length)
{
    if (!m || m->error[0]) return -1;
    if (!bindings || !length || bindings[0] < 0) { fail(m, "Invalid V2 persistent assignment"); return -1; }
    size_t at = 1;
    uint64_t count = (uint64_t) bindings[0];
    for (uint64_t i = 0; i < count; ++i) {
        if (at >= length || bindings[at] != HT_VAR || length - at < 5 || bindings[at + 1] < 0) {
            fail(m, "V2 assignment target is not a variable");
            return -1;
        }
        uint64_t uid = (uint64_t) bindings[at + 1];
        HTerm target = ht_lookup_uid(m->terms, uid);
        if (target == HT_NONE || ht_view(m->terms, target).tag != HT_VAR) { fail(m, "Unknown V2 assignment target"); return -1; }
        at += 5;
        size_t start = at;
        if (!skip_wire(bindings, length, &at)) { fail(m, "Malformed V2 assignment value"); return -1; }
        int64_t *wire = copy_array(bindings + start, at - start, sizeof(*wire));
        if (!wire) { fail(m, "V2 assignment allocation failed"); return -1; }
        if (!reserve(m, (void **) &m->assignments, &m->assignment_capacity, m->assignment_count + 1, sizeof(*m->assignments))) {
            free(wire);
            return -1;
        }
        m->assignments[m->assignment_count++] = (Assignment) { uid, wire, at - start };
    }
    if (at != length) { fail(m, "Trailing V2 assignment words"); return -1; }
    if (!apply_assignments(m)) {
        if (m->error[0]) return -1;
        m->action = ACTION_FAIL;
        m->assignment_failed = 1;
        m->answer_ready = 0;
        m->resume_answer = 0;
    }
    return 1;
}

int hol_v2_set_work_limit(HolV2Machine *m, uint64_t visits)
{
    if (!m) return -1;
    if (!visits) { m->api_error = "V2 atomic work limit must be positive"; return -1; }
    if (!ht_set_work_limit(m->terms, visits)) { m->api_error = ht_error(m->terms); return -1; }
    m->api_error = NULL;
    return 1;
}

uint64_t hol_v2_work_limit(const HolV2Machine *m)
{
    return m ? ht_work_limit(m->terms) : 0;
}

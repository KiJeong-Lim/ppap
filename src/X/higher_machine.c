#include "higher_machine.h"
#include "term.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

#define NONE SIZE_MAX
#define MAGIC INT64_C(0x484f4c31)
#define BATCH 4096

typedef struct {
    HTerm goal;
    size_t next, scope, hyps, barrier;
    uint64_t premises, call;
} Frame;

typedef struct { HTerm fact, rigid_head; size_t next; } Hypothesis;
/* next: the following fact of the same predicate, or of the dynamic facts.
    * peer: the following fact with the same first-argument key, or, for a fact
    * without a key, the following fact of the predicate without a key.
    * rigid is the head constant of a fact that has the literal clause shape and
    * a rigid head; head, body, binders and arity then describe that shape. No
    * binding reaches it, so it is read once, when the fact is loaded. */
typedef struct { int64_t symbol; HTerm fact; size_t next, peer; HTerm head, body, rigid; size_t binders, arity; } Fact;
typedef struct { size_t first, last, plain_first, plain_last, arity; unsigned char kinds, mixed; } Predicate;
/* literal == HT_NONE: the key is a constant symbol; otherwise the key is the
    * hash of the digits of that natural literal. */
typedef struct { size_t symbol, key; HTerm literal; size_t first, last; } Bucket;
typedef struct { int kind; size_t symbol; HTerm literal; } Key;
typedef struct { uint64_t target; int64_t *wire; size_t length; } Assignment;
typedef struct {
    HTCheckpoint terms;
    size_t work, hyps;
    uint64_t host;
} Checkpoint;
typedef struct {
    HTerm goal, head;
    size_t arity, global, keyed, unkeyed, dynamic, local, barrier;
    Frame frame;
    int phase, fallback, equality, plain;
} Search;
typedef struct {
    int kind;
    Checkpoint checkpoint;
    size_t work_head;
    Search search;
} Choice;

enum { ACTION_NEXT, ACTION_EXECUTE, ACTION_SEARCH, ACTION_FAIL, ACTION_ANSWER };
enum { CONTINUE_WORK, CONTINUE_IMPLY, CONTINUE_EQUALITY, CONTINUE_DEBUG, CONTINUE_ANSWER };
enum { SEARCH_GLOBAL, SEARCH_LOCAL, SEARCH_EQUAL_LOCAL, SEARCH_EQUAL_GLOBAL };
enum { KEY_NONE, KEY_NATURAL, KEY_CONSTANT, KEY_NOMINAL };
enum { LOAD_CREATE, LOAD_EXTEND, LOAD_QUERY };

struct HolV2Machine {
    HolTermStore *terms;
    int64_t *roles;
    size_t symbol_count, meta_count;
    Fact *facts;
    size_t fact_count, fact_capacity, dynamic_first, dynamic_last;
    Predicate *predicates;
    size_t predicate_count;
    Bucket *buckets;
    size_t bucket_count, bucket_capacity;
    size_t program_symbols, program_meta;
    uint64_t idle_uid;
    Search search;
    Checkpoint search_checkpoint;
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
    size_t batch, permanent, collect_at, collect_step, collections;
    uint64_t host_state, next_call, origin;
    int action, debugging, assignment_failed, exhausted, answer_ready, resume_answer, end_debugged;
    int event_kind, event_continuation, event_aux;
    HTerm event_term, truth;
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

static int grow(HolV2Machine *m, void **data, size_t *capacity, size_t count, size_t width);

static inline int reserve(HolV2Machine *m, void **data, size_t *capacity, size_t count, size_t width)
{
    return count <= *capacity || grow(m, data, capacity, count, width);
}

static int grow(HolV2Machine *m, void **data, size_t *capacity, size_t count, size_t width)
{
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

/* A role that only describes a constant. */
static int ordinary(int operation)
{
    return operation == HV2_ORDINARY || operation == HV2_ARITHMETIC || operation == HV2_NATURAL;
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
    if (m->truth != HT_NONE) return m->truth;
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

/* 1: the head of term, below its leading abstractions, is an unbound variable;
    * 0: it is anything else; -1: store error. Nothing is bound. */
static int flexible_head(HolV2Machine *m, HTerm term)
{
    HTerm body = ht_normalize(m->terms, term, HT_HNF);
    if (body == HT_NONE) return -1;
    for (;;) {
        HTView view = ht_view(m->terms, ht_deref(m->terms, body));
        if (view.tag != HT_LAM) break;
        body = view.a;
    }
    HTSpine spine;
    if (!ht_spine(m->terms, body, &spine)) return -1;
    int tag = ht_view(m->terms, ht_deref(m->terms, spine.head)).tag;
    ht_spine_free(&spine);
    return tag == HT_VAR || tag == HT_WILD;
}

#define PREFIX_LIMIT 32

/* The literal shape of a clause: pi (x\ pi (y\ ... head :- body)). Its
    * binders are instantiated together, and its body only after the head has
    * matched. Any other shape takes the general path of instantiate_fact. */
typedef struct {
    int is_type[PREFIX_LIMIT];
    int64_t meta[PREFIX_LIMIT];
    HTerm values[PREFIX_LIMIT];
    size_t count;
    HTerm head, body;
} Clause;

static HTerm rigid_head_of(const HolV2Machine *m, HTerm term, size_t *arity)
{
    size_t budget = 4096;
    *arity = 0;
    for (;;) {
        term = ht_deref(m->terms, term);
        HTView view = ht_view(m->terms, term);
        if (view.tag != HT_APP) return view.tag == HT_CONST || view.tag == HT_NOMINAL ? term : HT_NONE;
        if (!budget--) return HT_NONE;
        ++*arity;
        term = view.a;
    }
}

static void clause_shape(const HolV2Machine *m, HTerm fact, Clause *clause)
{
    HTerm term = ht_deref(m->terms, fact);
    clause->count = 0;
    while (clause->count < PREFIX_LIMIT) {
        HTView application = ht_view(m->terms, term);
        if (application.tag != HT_APP || ht_view(m->terms, ht_deref(m->terms, application.a)).tag != HT_CONST) break;
        int operation = role(m, application.a);
        HTView function = ht_view(m->terms, ht_deref(m->terms, application.b));
        if ((operation != HV2_PI && operation != HV2_TY_PI) || function.tag != HT_LAM) break;
        clause->is_type[clause->count] = operation == HV2_TY_PI;
        clause->meta[clause->count] = function.meta;
        ++clause->count;
        term = ht_deref(m->terms, function.a);
    }
    clause->head = HT_NONE;
    clause->body = HT_NONE;
    HTView outer = ht_view(m->terms, term);
    HTView inner = ht_view(m->terms, outer.tag == HT_APP ? ht_deref(m->terms, outer.a) : HT_NONE);
    size_t arity;
    if (inner.tag == HT_APP && ht_view(m->terms, ht_deref(m->terms, inner.a)).tag == HT_CONST && role(m, inner.a) == HV2_IF) {
        clause->head = inner.b;
        clause->body = outer.b;
    } else {
        HTerm head = rigid_head_of(m, term, &arity);
        if (head != HT_NONE && (ht_view(m->terms, head).tag == HT_NOMINAL || ordinary(role(m, head)))) clause->head = term;
    }
}

/* Two arguments whose rigid heads differ cannot unify, and neither can two
    * different naturals. A natural against a successor term, and an opaque
    * formula, are compared by the unifier alone. */
static int rigid_clash(const HolV2Machine *m, HTerm goal, HTerm pattern)
{
    size_t arity;
    HTView number = ht_view(m->terms, ht_deref(m->terms, goal)), other = ht_view(m->terms, ht_deref(m->terms, pattern));
    if (number.tag == HT_NAT && other.tag == HT_NAT) return strcmp(number.digits, other.digits) != 0;
    HTerm left = rigid_head_of(m, goal, &arity), right = rigid_head_of(m, pattern, &arity);
    if (left == HT_NONE || right == HT_NONE) return 0;
    HTView lhs = ht_view(m->terms, left), rhs = ht_view(m->terms, right);
    if ((lhs.tag == HT_CONST && !ordinary(role(m, left))) || (rhs.tag == HT_CONST && !ordinary(role(m, right)))) return 0;
    if (lhs.tag != rhs.tag) return 1;
    return lhs.tag == HT_CONST ? lhs.symbol != rhs.symbol : lhs.uid != rhs.uid;
}

/* Whether a literal clause head, with the rigid head and the arity it has, is
    * certain not to match the goal of a plain search. */
static int shape_clash(const HolV2Machine *m, const Search *search, HTerm clause_head, HTerm head, size_t arity)
{
    if (!same_head(m, search->head, head)) return 1;
    if (arity != search->arity) return 0;
    HTerm goal = ht_deref(m->terms, search->goal), pattern = ht_deref(m->terms, clause_head);
    while (arity--) {
        HTView left = ht_view(m->terms, goal), right = ht_view(m->terms, pattern);
        if (left.tag != HT_APP || right.tag != HT_APP) return 0;
        if (rigid_clash(m, left.b, right.b)) return 1;
        goal = ht_deref(m->terms, left.a);
        pattern = ht_deref(m->terms, right.a);
    }
    return 0;
}

/* Whether a clause head of this literal shape is certain not to match. */
static int head_clash(const HolV2Machine *m, const Search *search, HTerm fact)
{
    Clause clause;
    if (!search->plain) return 0;
    clause_shape(m, fact, &clause);
    if (clause.head == HT_NONE) return 0;
    size_t arity;
    HTerm head = rigid_head_of(m, clause.head, &arity);
    return head != HT_NONE && shape_clash(m, search, clause.head, head, arity);
}

static int fact_clash(const HolV2Machine *m, const Search *search, const Fact *fact)
{
    if (fact->rigid == HT_NONE) return head_clash(m, search, fact->fact);
    return search->plain && shape_clash(m, search, fact->head, fact->rigid, fact->arity);
}

/* What an argument shows without being reduced: a natural literal, or the
    * rigid head of an application. rigid_clash decides by exactly these. */
static Key argument_key(const HolV2Machine *m, HTerm argument)
{
    HTerm term = ht_deref(m->terms, argument);
    if (ht_view(m->terms, term).tag == HT_NAT) return (Key) { KEY_NATURAL, 0, term };
    size_t arity;
    HTerm head = rigid_head_of(m, term, &arity);
    if (head == HT_NONE) return (Key) { KEY_NONE, 0, HT_NONE };
    HTView view = ht_view(m->terms, head);
    if (view.tag == HT_NOMINAL) return (Key) { KEY_NOMINAL, 0, HT_NONE };
    return ordinary(role(m, head)) ? (Key) { KEY_CONSTANT, view.symbol, HT_NONE } : (Key) { KEY_NONE, 0, HT_NONE };
}

/* The first argument of a literal application with arity >= 1 arguments. */
static HTerm first_argument(const HolV2Machine *m, HTerm term, size_t arity)
{
    term = ht_deref(m->terms, term);
    while (arity-- > 1) term = ht_deref(m->terms, ht_view(m->terms, term).a);
    return ht_view(m->terms, term).b;
}

static size_t key_value(const HolV2Machine *m, Key key)
{
    if (key.kind != KEY_NATURAL) return key.symbol;
    uint64_t hash = UINT64_C(1469598103934665603);
    for (const char *digit = ht_view(m->terms, key.literal).digits; *digit; ++digit) hash = (hash ^ (unsigned char) *digit) * UINT64_C(1099511628211);
    return (size_t) hash;
}

static size_t bucket_home(size_t symbol, size_t value, int natural, size_t capacity)
{
    uint64_t hash = ((uint64_t) symbol + 1) * UINT64_C(0x9E3779B97F4A7C15) ^ ((uint64_t) value + (natural ? UINT64_C(0x632BE59BD9B4E019) : 0));
    return (size_t) ((hash * UINT64_C(11400714819323198485)) >> 20) & (capacity - 1);
}

/* The bucket of a natural or constant key under a predicate, or the empty
    * slot (first == NONE) where it belongs. NULL: there is no table yet. */
static Bucket *find_bucket(const HolV2Machine *m, size_t symbol, Key key)
{
    if (!m->bucket_capacity) return NULL;
    const char *digits = key.kind == KEY_NATURAL ? ht_view(m->terms, key.literal).digits : NULL;
    size_t value = key_value(m, key);
    for (size_t at = bucket_home(symbol, value, digits != NULL, m->bucket_capacity);; at = (at + 1) & (m->bucket_capacity - 1)) {
        Bucket *bucket = &m->buckets[at];
        if (bucket->first == NONE) return bucket;
        if (bucket->symbol != symbol || bucket->key != value || (bucket->literal == HT_NONE) != (digits == NULL)) continue;
        if (!digits || !strcmp(ht_view(m->terms, bucket->literal).digits, digits)) return bucket;
    }
}

static int reserve_buckets(HolV2Machine *m)
{
    if (m->bucket_capacity && m->bucket_count < m->bucket_capacity / 2) return 1;
    size_t capacity = m->bucket_capacity ? m->bucket_capacity * 2 : 64;
    if (capacity < m->bucket_capacity || capacity > SIZE_MAX / sizeof(Bucket)) return fail(m, "V2 fact index overflow");
    Bucket *table = malloc(capacity * sizeof(*table));
    if (!table) return fail(m, "V2 fact index allocation failed");
    for (size_t i = 0; i < capacity; ++i) table[i] = (Bucket) { 0, 0, HT_NONE, NONE, NONE };
    for (size_t i = 0; i < m->bucket_capacity; ++i) {
        Bucket bucket = m->buckets[i];
        if (bucket.first == NONE) continue;
        size_t at = bucket_home(bucket.symbol, bucket.key, bucket.literal != HT_NONE, capacity);
        while (table[at].first != NONE) at = (at + 1) & (capacity - 1);
        table[at] = bucket;
    }
    free(m->buckets);
    m->buckets = table;
    m->bucket_capacity = capacity;
    return 1;
}

/* Files the newest fact under its predicate, after the older ones. A fact
    * whose head is literally the predicate applied to arguments has the key of
    * its first argument when that is a natural or has an ordinary constant head.
    * A predicate whose keyed facts differ in arity, or have keys of both kinds,
    * is searched without the index. */
static int index_fact(HolV2Machine *m, size_t at)
{
    Fact *fact = &m->facts[at];
    Clause clause;
    size_t arity = 0;
    clause_shape(m, fact->fact, &clause);
    HTerm head = clause.head == HT_NONE ? HT_NONE : rigid_head_of(m, clause.head, &arity);
    fact->next = NONE;
    fact->peer = NONE;
    fact->rigid = head;
    if (head != HT_NONE) {
        fact->head = clause.head;
        fact->body = clause.body;
        fact->binders = clause.count;
        fact->arity = arity;
    }
    if (fact->symbol < 0) {
        if (m->dynamic_last == NONE) m->dynamic_first = at;
        else m->facts[m->dynamic_last].next = at;
        m->dynamic_last = at;
        return 1;
    }
    Predicate *predicate = &m->predicates[fact->symbol];
    if (predicate->last == NONE) predicate->first = at;
    else m->facts[predicate->last].next = at;
    predicate->last = at;
    Key key = { KEY_NONE, 0, HT_NONE };
    if (head != HT_NONE && arity) {
        HTView view = ht_view(m->terms, head);
        if (view.tag == HT_CONST && view.symbol == (size_t) fact->symbol) key = argument_key(m, first_argument(m, clause.head, arity));
    }
    if (key.kind != KEY_NATURAL && key.kind != KEY_CONSTANT) {
        if (predicate->plain_last == NONE) predicate->plain_first = at;
        else m->facts[predicate->plain_last].peer = at;
        predicate->plain_last = at;
        return 1;
    }
    if (predicate->arity == NONE) predicate->arity = arity;
    else if (predicate->arity != arity) predicate->mixed = 1;
    predicate->kinds |= key.kind == KEY_NATURAL ? 1 : 2;
    if (predicate->kinds == 3) predicate->mixed = 1;
    if (!reserve_buckets(m)) return 0;
    Bucket *bucket = find_bucket(m, (size_t) fact->symbol, key);
    if (bucket->first == NONE) {
        *bucket = (Bucket) { (size_t) fact->symbol, key_value(m, key), key.literal, at, at };
        ++m->bucket_count;
    } else {
        m->facts[bucket->last].peer = at;
        bucket->last = at;
    }
    return 1;
}

/* The candidates of a search come from up to four chains in source order. */
static size_t next_fact(const Search *search)
{
    size_t candidate = search->global < search->dynamic ? search->global : search->dynamic;
    if (search->keyed < candidate) candidate = search->keyed;
    return search->unkeyed < candidate ? search->unkeyed : candidate;
}

static void advance_fact(const HolV2Machine *m, Search *search, size_t candidate)
{
    if (candidate == search->global) search->global = m->facts[candidate].next;
    else if (candidate == search->keyed) search->keyed = m->facts[candidate].peer;
    else if (candidate == search->unkeyed) search->unkeyed = m->facts[candidate].peer;
    else search->dynamic = m->facts[candidate].next;
}

static int instantiate_head(HolV2Machine *m, HTerm fact, size_t scope, Clause *clause, HTerm *head)
{
    clause_shape(m, fact, clause);
    if (clause->head == HT_NONE) return 0;
    for (size_t i = 0; i < clause->count; ++i) {
        clause->values[i] = ht_var(m->terms, scope, clause->is_type[i], clause->meta[i]);
        if (!term_ok(m, clause->values[i])) return -1;
    }
    *head = clause->count ? ht_instantiate(m->terms, clause->head, clause->values, clause->count) : clause->head;
    return term_ok(m, *head) ? 1 : -1;
}

/* instantiate_head for a fact whose shape was read when it was loaded. */
static int instantiate_known(HolV2Machine *m, const Fact *fact, size_t scope, Clause *clause, HTerm *head)
{
    clause->count = fact->binders;
    clause->head = fact->head;
    clause->body = fact->body;
    HTerm term = ht_deref(m->terms, fact->fact);
    for (size_t i = 0; i < fact->binders; ++i) {
        HTView application = ht_view(m->terms, term);
        HTView function = ht_view(m->terms, ht_deref(m->terms, application.b));
        clause->values[i] = ht_var(m->terms, scope, role(m, application.a) == HV2_TY_PI, function.meta);
        if (!term_ok(m, clause->values[i])) return -1;
        term = ht_deref(m->terms, function.a);
    }
    *head = fact->binders ? ht_instantiate(m->terms, fact->head, clause->values, fact->binders) : fact->head;
    return term_ok(m, *head) ? 1 : -1;
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

static int search_has_alternative(const Search *search)
{
    if (search->phase == SEARCH_GLOBAL || search->phase == SEARCH_EQUAL_GLOBAL) {
        return next_fact(search) != NONE || (search->phase == SEARCH_GLOBAL && search->local != NONE);
    }
    return search->local != NONE || (search->phase == SEARCH_EQUAL_LOCAL && search->fallback);
}

static void schedule_search(HolV2Machine *m, Search search, Checkpoint saved)
{
    m->search = search;
    m->search_checkpoint = saved;
    m->action = ACTION_SEARCH;
}

/* Advances past candidates that are certain not to match in the state of the
    * search checkpoint. Later bindings only add clashes, so a resumed
    * alternative skips them soundly. Every skipped candidate consumes the
    * scheduler batch like a failed trial; 0 reports an exhausted batch. */
static int skip_excluded(HolV2Machine *m, Search *search)
{
    if (!search->plain) return 1;
    if (search->phase == SEARCH_GLOBAL || search->phase == SEARCH_EQUAL_GLOBAL) {
        for (;;) {
            size_t candidate = next_fact(search);
            if (candidate == NONE) break;
            if (m->batch >= BATCH) return 0;
            if (!fact_clash(m, search, &m->facts[candidate])) return 1;
            ++m->batch;
            advance_fact(m, search, candidate);
        }
        if (search->phase == SEARCH_EQUAL_GLOBAL) return 1;
    }
    while (search->local != NONE) {
        Hypothesis candidate = m->hyps[search->local];
        if (m->batch >= BATCH) return 0;
        int excluded = candidate.rigid_head != HT_NONE && !same_head(m, search->head, candidate.rigid_head);
        if (!excluded && !head_clash(m, search, candidate.fact)) return 1;
        ++m->batch;
        search->local = candidate.next;
    }
    return 1;
}

/* One candidate or phase transition per scheduler step permits cancellation. */
static int search_step(HolV2Machine *m)
{
    Search *search = &m->search;
    Checkpoint saved = m->search_checkpoint;
    if (!restore_checkpoint(m, saved)) return 0;
    if (!skip_excluded(m, search)) return 1;
    HTerm fact;
    const Fact *known = NULL;
    if (search->phase == SEARCH_GLOBAL || search->phase == SEARCH_EQUAL_GLOBAL) {
        size_t candidate = next_fact(search);
        if (candidate == NONE) {
            if (search->phase == SEARCH_EQUAL_GLOBAL) return 0;
            search->phase = SEARCH_LOCAL;
            return 1;
        }
        fact = m->facts[candidate].fact;
        if (m->facts[candidate].rigid != HT_NONE) known = &m->facts[candidate];
        advance_fact(m, search, candidate);
    } else {
        if (search->local != NONE) {
            Hypothesis candidate = m->hyps[search->local];
            search->local = candidate.next;
            if (candidate.rigid_head != HT_NONE && !same_head(m, search->head, candidate.rigid_head)) return 1;
            fact = candidate.fact;
        } else if (search->phase == SEARCH_EQUAL_LOCAL && search->fallback) {
            if (search->equality == 2) {
                m->work_head = search->frame.next;
                m->action = ACTION_NEXT;
                return 1;
            }
            if (search->equality == 3) return 0;
            search->phase = SEARCH_EQUAL_GLOBAL;
            return 1;
        } else {
            return 0;
        }
    }
    skip_excluded(m, search);
    Clause clause;
    HTerm head = HT_NONE, body = HT_NONE;
    int literal, matches;
    size_t arity;
    if (known) {
        /* the head is the rigid application that the fact was loaded with */
        literal = instantiate_known(m, known, search->frame.scope, &clause, &head);
        if (literal < 0) return 0;
        matches = same_head(m, search->head, known->rigid);
        arity = known->arity;
    } else {
        literal = instantiate_head(m, fact, search->frame.scope, &clause, &head);
        if (literal < 0 || (!literal && !instantiate_fact(m, fact, search->frame.scope, &head, &body))) return 0;
        HTSpine spine;
        if (!normalized_spine(m, head, &spine)) return fail(m, ht_error(m->terms));
        matches = same_head(m, search->head, spine.head);
        arity = spine.count;
        ht_spine_free(&spine);
    }
    if (!matches) return 1;
    if (arity != search->arity) return fail(m, "V2 clause head has inconsistent arity");
    int unified = ht_unify(m->terms, search->goal, head);
    if (unified < 0) return fail(m, ht_error(m->terms));
    if (!unified) return 1;
    if (literal) {
        body = clause.body == HT_NONE ? true_term(m) : clause.count ? ht_instantiate(m->terms, clause.body, clause.values, clause.count) : clause.body;
        if (!term_ok(m, body)) return 0;
    }
    Search alternative = *search;
    if (alternative.phase == SEARCH_EQUAL_LOCAL) alternative.fallback = 0;
    if (search_has_alternative(&alternative)) {
        Choice choice = { 0 };
        choice.kind = 1;
        choice.checkpoint = saved;
        choice.search = alternative;
        if (!push_choice(m, choice)) return 0;
    }
    Frame environment = search->frame;
    environment.barrier = search->barrier;
    if (!schedule(m, body, environment, environment.next)) return 0;
    m->current = environment;
    if (m->host_state) event(m, HV2_EVENT_SETTLE, HT_NONE, CONTINUE_WORK, 0);
    return 1;
}

/* goal is the spine of the current goal when the caller has it. */
static int begin_search(HolV2Machine *m, int equality, const HTSpine *goal)
{
    HTSpine spine;
    if (!goal && !normalized_spine(m, m->current.goal, &spine)) return fail(m, ht_error(m->terms));
    HTerm head = goal ? goal->head : spine.head;
    size_t arity = goal ? goal->count : spine.count;
    if (!goal) ht_spine_free(&spine);
    HTView view = ht_view(m->terms, ht_deref(m->terms, head));
    if (view.tag != HT_CONST && view.tag != HT_NOMINAL) return fail(m, "Bad V2 goal: predicate head is not rigid");
    if (m->next_call >= INT64_MAX) return fail(m, "V2 call identity exhausted");
    Search search = { 0 };
    search.goal = m->current.goal;
    search.head = head;
    search.arity = arity;
    size_t plain_arity;
    search.plain = rigid_head_of(m, search.goal, &plain_arity) != HT_NONE && plain_arity == search.arity;
    search.global = NONE;
    search.keyed = NONE;
    search.unkeyed = NONE;
    if (view.tag == HT_CONST && view.symbol < m->predicate_count) {
        /* A keyed fact that the index leaves out has a first argument that
            * clashes with the goal's, so head_clash would have skipped it. */
        const Predicate *predicate = &m->predicates[view.symbol];
        Key key = { KEY_NONE, 0, HT_NONE };
        if (search.plain && predicate->kinds && !predicate->mixed && search.arity == predicate->arity) key = argument_key(m, first_argument(m, search.goal, search.arity));
        if ((predicate->kinds == 1 && key.kind == KEY_NATURAL) || (predicate->kinds == 2 && (key.kind == KEY_CONSTANT || key.kind == KEY_NOMINAL))) {
            const Bucket *bucket = key.kind == KEY_NOMINAL ? NULL : find_bucket(m, view.symbol, key);
            if (bucket) search.keyed = bucket->first;
            search.unkeyed = predicate->plain_first;
        } else {
            search.global = predicate->first;
        }
    }
    search.dynamic = m->dynamic_first;
    search.local = m->current.hyps;
    search.barrier = m->choice_count;
    search.frame = m->current;
    search.frame.call = m->next_call++;
    search.phase = equality ? SEARCH_EQUAL_LOCAL : SEARCH_GLOBAL;
    search.fallback = equality != 0;
    search.equality = equality;
    schedule_search(m, search, checkpoint(m));
    return 1;
}

static int backtrack_step(HolV2Machine *m)
{
    m->event_kind = 0;
    m->end_debugged = 0;
    if (!m->choice_count) {
        m->exhausted = 1;
        return 0;
    }
    Choice choice = m->choices[--m->choice_count];
    if (!restore_checkpoint(m, choice.checkpoint)) return !m->error[0];
    if (choice.kind == 0) {
        m->work_head = choice.work_head;
        m->action = ACTION_NEXT;
    } else {
        schedule_search(m, choice.search, choice.checkpoint);
    }
    return 1;
}

/* Unknown or computational heads retain ordinary matching, without a hint. */
static HTerm rigid_fact_head(const HolV2Machine *m, HTerm fact)
{
    size_t budget = 128;
    while (budget) {
        size_t arity = 0;
        HTerm first = HT_NONE, head = fact;
        HTView view;
        for (;;) {
            if (!budget) return HT_NONE;
            --budget;
            view = ht_view(m->terms, head);
            if (view.tag != HT_APP) break;
            first = view.b;
            head = view.a;
            ++arity;
        }
        if (view.tag == HT_NOMINAL) return head;
        if (view.tag != HT_CONST) return HT_NONE;
        int operation = role(m, head);
        if ((operation == HV2_PI || operation == HV2_TY_PI) && arity == 1) {
            HTView binder = ht_view(m->terms, first);
            if (binder.tag != HT_LAM) return HT_NONE;
            fact = binder.a;
        } else if (operation == HV2_IF && arity == 2) {
            fact = first;
        } else {
            return head;
        }
    }
    return HT_NONE;
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
            m->hyps[m->hyp_count] = (Hypothesis) { expanded[i - 1], rigid_fact_head(m, expanded[i - 1]), hyps };
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

/* 1: the host would leave the equality to the search without reading a state;
    * 0: the host decides; -1: store error. */
static int plain_equality(HolV2Machine *m, const HTSpine *spine)
{
    HTerm type = ht_normalize(m->terms, spine->args[0], HT_HNF);
    if (type == HT_NONE) return -1;
    if (role(m, type) == HV2_NATURAL) return 0;
    for (size_t i = 1; i < 3; ++i) {
        int arithmetic = ht_mentions_arithmetic(m->terms, spine->args[i]);
        if (arithmetic) return arithmetic < 0 ? -1 : 0;
    }
    return 1;
}

/* 1: the antecedent is a conjunction of atoms and clauses with ordinary heads,
    * to which the host would add no premise; 0: the host decides; -1: store error. */
static int plain_antecedent(HolV2Machine *m, HTerm fact, size_t depth)
{
    HTSpine spine;
    if (depth > 64) return 0;
    if (!normalized_spine(m, fact, &spine)) return -1;
    int tag = ht_view(m->terms, ht_deref(m->terms, spine.head)).tag;
    int operation = role(m, spine.head);
    int plain = tag == HT_NOMINAL || (tag == HT_CONST && (operation == HV2_ORDINARY || operation == HV2_IF));
    if (tag == HT_CONST && operation == HV2_AND && spine.count == 2) {
        plain = plain_antecedent(m, spine.args[0], depth + 1);
        if (plain == 1) plain = plain_antecedent(m, spine.args[1], depth + 1);
    }
    ht_spine_free(&spine);
    return plain;
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
            else {
                int plain = plain_antecedent(m, spine.args[0], 0);
                if (plain < 0) success = fail(m, ht_error(m->terms));
                else if (plain) success = enter_implication(m, m->current.premises);
                else success = event(m, HV2_EVENT_IMPLY, spine.args[0], CONTINUE_IMPLY, 0);
            }
            break;
        case HV2_EQ:
            if (arity != 3) success = fail(m, "Malformed V2 equality");
            else {
                int plain = plain_equality(m, &spine);
                if (plain < 0) success = fail(m, ht_error(m->terms));
                else if (plain) success = begin_search(m, 4, &spine);
                else success = event(m, HV2_EVENT_EQUALITY, m->current.goal, CONTINUE_EQUALITY, 0);
            }
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
        case HV2_FLEX:
            /* arguments: the type instance, then the term */
            if (arity != 2) success = fail(m, "Malformed V2 flex goal");
            else {
                int flexible = flexible_head(m, spine.args[1]);
                success = flexible < 0 ? fail(m, ht_error(m->terms)) : flexible;
            }
            break;
        case HV2_TY_PI:
        case HV2_IF:
            success = fail(m, "A V2 clause operator appeared as a goal");
            break;
        default:
            success = begin_search(m, 0, &spine);
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

static _Atomic uint64_t next_origin = 1;

static int add_symbols(HolV2Machine *m, const int64_t *roles, size_t total)
{
    if (total == m->symbol_count) return 1;
    int64_t *grown = total <= SIZE_MAX / sizeof(*grown) ? realloc(m->roles, total * sizeof(*grown)) : NULL;
    if (!grown) return fail(m, "V2 symbol allocation failed");
    m->roles = grown;
    for (size_t first = m->symbol_count, i = first; i < total; ++i) {
        int64_t operation = roles[i - first];
        if (operation < HV2_ORDINARY || operation > HV2_NATURAL) return fail(m, "Invalid V2 symbol role");
        if (operation == HV2_SUCCESSOR && m->truth != HT_NONE) return fail(m, "A V2 fragment declares another successor symbol");
        m->roles[i] = operation;
        m->symbol_count = i + 1;
        if (operation == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, i)) return fail(m, ht_error(m->terms));
        if (operation == HV2_ARITHMETIC && !ht_set_arithmetic_symbol(m->terms, i)) return fail(m, ht_error(m->terms));
        if (operation == HV2_SUCCESSOR) ht_set_successor(m->terms, i);
    }
    return 1;
}

static int grow_predicates(HolV2Machine *m, size_t count)
{
    if (count <= m->predicate_count) return 1;
    Predicate *grown = count <= SIZE_MAX / sizeof(*grown) ? realloc(m->predicates, count * sizeof(*grown)) : NULL;
    if (!grown) return fail(m, "V2 predicate index allocation failed");
    m->predicates = grown;
    while (m->predicate_count < count) m->predicates[m->predicate_count++] = (Predicate) { NONE, NONE, NONE, NONE, NONE, 0, 0 };
    return 1;
}

static HTerm template_term(HolV2Machine *m, const int64_t *row, size_t at, const HTerm *roots, const int64_t *digits, size_t remaining)
{
    if (row[3] || row[4] || !valid_meta(row[5], m->meta_count)) {
        fail(m, "Invalid V2 template metadata or reserved operand");
        return HT_NONE;
    }
    HTerm value = HT_NONE;
    switch (row[0]) {
        case 0:
            if (valid_index(row[1], m->query_count) && row[2] == 0) value = m->query[row[1]];
            break;
        case 1:
            if (valid_index(row[1], m->symbol_count) && row[2] == 0) value = ht_constant(m->terms, (size_t) row[1], row[5]);
            break;
        case 2:
            if (valid_index(row[1], at) && valid_index(row[2], at)) value = ht_app(m->terms, roots[row[1]], roots[row[2]], row[5]);
            break;
        case 3:
            if (row[1] >= 0 && (uint64_t) row[1] <= SIZE_MAX && row[2] == 0) value = ht_index(m->terms, (size_t) row[1]);
            break;
        case 4:
            if (valid_index(row[1], at) && row[2] == 0) value = ht_lam(m->terms, roots[row[1]], row[5]);
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
    }
    return value;
}

/* Reads one wordcode fragment. LOAD_CREATE and LOAD_EXTEND add it to the
    * program; LOAD_QUERY builds it above the program, for one run. */
static int load(HolV2Machine *m, const int64_t *code, size_t length, int mode)
{
    if (!code || length < 8 || code[0] != MAGIC || code[1] != 2) return fail(m, "Invalid V2 wordcode header");
    for (size_t i = 2; i < 8; ++i) {
        if (i == 6 && mode == LOAD_EXTEND) continue;
        if (code[i] < 0 || (uint64_t) code[i] > SIZE_MAX) return fail(m, "Invalid V2 wordcode count");
    }
    size_t term_count = (size_t) code[2], symbol_total = (size_t) code[3], fact_count = (size_t) code[4], query_count = (size_t) code[5];
    if (symbol_total < m->symbol_count) return fail(m, "V2 wordcode has fewer symbols than its machine");
    if (mode == LOAD_EXTEND && (query_count || code[6] != -1)) return fail(m, "A V2 program fragment has a query");
    if (mode == LOAD_QUERY && fact_count) return fail(m, "A V2 query fragment has clauses");
    size_t symbol_count = symbol_total - m->symbol_count;
    size_t remaining = length - 8;
    if (query_count > remaining / 2) return fail(m, "Truncated V2 query table");
    const int64_t *queries = code + 8;
    remaining -= 2 * query_count;
    if (symbol_count > remaining) return fail(m, "Truncated V2 symbol table");
    const int64_t *roles = queries + 2 * query_count;
    remaining -= symbol_count;
    if (term_count > remaining / 6) return fail(m, "Truncated V2 template table");
    const int64_t *templates = roles + symbol_count;
    remaining -= term_count * 6;
    if (fact_count > remaining / 2) return fail(m, "Truncated V2 clause table");
    const int64_t *facts = templates + term_count * 6;
    remaining -= fact_count * 2;
    const int64_t *digits = facts + fact_count * 2;
    if (mode != LOAD_EXTEND && !valid_index(code[6], term_count)) return fail(m, "Invalid V2 query root");
    m->meta_count = (size_t) code[7];
    if (!add_symbols(m, roles, symbol_total)) return 0;
    if (mode == LOAD_CREATE) {
        int has_true = 0, has_successor = 0;
        for (size_t i = 0; i < m->symbol_count; ++i) {
            if (m->roles[i] == HV2_TRUE) has_true = 1;
            if (m->roles[i] == HV2_SUCCESSOR) has_successor = 1;
        }
        if (!has_true || !has_successor) return fail(m, "V2 requires true and successor symbols");
        m->truth = true_term(m);
        if (!term_ok(m, m->truth)) return 0;
    }
    if (query_count > SIZE_MAX / sizeof(*m->query)) return fail(m, "V2 query allocation overflow");
    m->query = query_count ? calloc(query_count, sizeof(*m->query)) : NULL;
    if (query_count && !m->query) return fail(m, "V2 query allocation failed");
    for (size_t i = 0; i < query_count; ++i) {
        if ((queries[2 * i] != 0 && queries[2 * i] != 1) || !valid_meta(queries[2 * i + 1], m->meta_count)) return fail(m, "Invalid V2 query descriptor");
        m->query[i] = ht_var(m->terms, 0, (int) queries[2 * i], queries[2 * i + 1]);
        m->query_count = i + 1;
        if (!term_ok(m, m->query[i])) return 0;
    }
    HTerm *roots = term_count <= SIZE_MAX / sizeof(*roots) ? malloc((term_count ? term_count : 1) * sizeof(*roots)) : NULL;
    if (!roots) return fail(m, "V2 template allocation failed");
    for (size_t i = 0; !m->error[0] && i < term_count; ++i) roots[i] = template_term(m, templates + 6 * i, i, roots, digits, remaining);
    if (!m->error[0] && fact_count) {
        if (fact_count > SIZE_MAX - m->fact_count) fail(m, "V2 fact allocation overflow");
        else if (reserve(m, (void **) &m->facts, &m->fact_capacity, m->fact_count + fact_count, sizeof(*m->facts))) grow_predicates(m, m->symbol_count);
    }
    for (size_t i = 0; !m->error[0] && i < fact_count; ++i) {
        int64_t symbol = facts[2 * i], root = facts[2 * i + 1];
        if ((symbol != -1 && !valid_index(symbol, m->symbol_count)) || !valid_index(root, term_count)) fail(m, "Invalid V2 fact descriptor");
        else {
            m->facts[m->fact_count] = (Fact) { symbol, roots[root], NONE, NONE, HT_NONE, HT_NONE, HT_NONE, 0, 0 };
            index_fact(m, m->fact_count++);
        }
    }
    if (!m->error[0] && mode != LOAD_EXTEND) {
        Frame initial = { roots[code[6]], NONE, 0, NONE, 0, 0, 0 };
        m->work_head = push_frame(m, initial);
        m->current = initial;
        m->exhausted = 0;
    }
    if (mode != LOAD_QUERY) {
        m->permanent = ht_heap_count(m->terms);
        m->idle_uid = ht_next_uid(m->terms);
        m->program_symbols = m->symbol_count;
        m->program_meta = m->meta_count;
        if (!m->error[0]) ht_seal(m->terms);
    }
    hol_v2_set_collection_step(m, 65536);
    free(roots);
    return !m->error[0];
}

HolV2Machine *hol_v2_create(const int64_t *code, size_t length)
{
    HolV2Machine *m = calloc(1, sizeof(*m));
    if (!m) return NULL;
    m->work_head = NONE;
    m->dynamic_first = NONE;
    m->dynamic_last = NONE;
    m->truth = HT_NONE;
    m->next_call = 1;
    m->origin = atomic_fetch_add(&next_origin, 1);
    if (!m->origin) { fail(m, "V2 runtime identity exhausted"); return m; }
    m->terms = ht_create();
    if (!m->terms) { fail(m, "V2 term store allocation failed"); return m; }
    load(m, code, length, LOAD_CREATE);
    return m;
}

static void release_spare(void **data, size_t *capacity, size_t limit)
{
    if (*capacity > limit) {
        free(*data);
        *data = NULL;
        *capacity = 0;
    }
}

/* Leaves the run. The program stays; everything else is as a machine created
    * from that program alone would have it, so the next run numbers its
    * variables, calls and host states from the same origin. A snapshot of the
    * run that was left can no longer be restored. */
static int leave_run(HolV2Machine *m)
{
    if (m->error[0]) return 0;
    if (!ht_reset(m->terms, m->permanent, m->idle_uid, m->program_symbols)) return fail(m, ht_error(m->terms));
    m->symbol_count = m->program_symbols;
    m->meta_count = m->program_meta;
    for (size_t i = 0; i < m->assignment_count; ++i) free(m->assignments[i].wire);
    m->assignment_count = 0;
    free(m->query);
    m->query = NULL;
    m->query_count = 0;
    m->work_count = 0;
    m->hyp_count = 0;
    m->choice_count = 0;
    m->buffer_count = 0;
    m->work_head = NONE;
    memset(&m->search, 0, sizeof(m->search));
    memset(&m->search_checkpoint, 0, sizeof(m->search_checkpoint));
    memset(&m->current, 0, sizeof(m->current));
    m->batch = 0;
    m->collections = 0;
    m->host_state = 0;
    m->next_call = 1;
    m->action = ACTION_NEXT;
    m->debugging = 0;
    m->assignment_failed = 0;
    m->exhausted = 1;
    m->answer_ready = 0;
    m->resume_answer = 0;
    m->end_debugged = 0;
    m->event_kind = 0;
    m->event_continuation = 0;
    m->event_aux = 0;
    m->event_term = HT_NONE;
    m->api_error = NULL;
    m->origin = atomic_fetch_add(&next_origin, 1);
    if (!m->origin) return fail(m, "V2 runtime identity exhausted");
    release_spare((void **) &m->work, &m->work_capacity, 4096);
    release_spare((void **) &m->hyps, &m->hyp_capacity, 4096);
    release_spare((void **) &m->choices, &m->choice_capacity, 4096);
    release_spare((void **) &m->buffer, &m->buffer_capacity, 4096);
    release_spare((void **) &m->assignments, &m->assignment_capacity, 4096);
    hol_v2_set_collection_step(m, 65536);
    return 1;
}

int hol_v2_extend(HolV2Machine *m, const int64_t *code, size_t length)
{
    return m && leave_run(m) && load(m, code, length, LOAD_EXTEND) ? 1 : -1;
}

int hol_v2_query(HolV2Machine *m, const int64_t *code, size_t length)
{
    return m && leave_run(m) && load(m, code, length, LOAD_QUERY) ? 1 : -1;
}

int hol_v2_idle(HolV2Machine *m)
{
    return m && leave_run(m) ? 1 : -1;
}

typedef struct {
    HolV2Machine *machine;
    unsigned char *frames, *hyps;
    size_t *frame_forward, *hyp_forward;
} Collection;

static void keep_hyps(Collection *c, size_t at)
{
    for (; at != NONE && !c->hyps[at]; at = c->machine->hyps[at].next) c->hyps[at] = 1;
}

static void keep_frames(Collection *c, size_t at)
{
    for (; at != NONE && !c->frames[at]; at = c->machine->work[at].next) {
        c->frames[at] = 1;
        keep_hyps(c, c->machine->work[at].hyps);
    }
}

static void collect_mark(HTCollection *terms, void *context)
{
    Collection *c = context;
    HolV2Machine *m = c->machine;
    for (size_t i = 0; i < m->query_count; ++i) ht_collect_mark(terms, m->query[i]);
    for (size_t i = 0; i < m->work_count; ++i) if (c->frames[i]) ht_collect_mark(terms, m->work[i].goal);
    for (size_t i = 0; i < m->hyp_count; ++i) {
        if (!c->hyps[i]) continue;
        ht_collect_mark(terms, m->hyps[i].fact);
        ht_collect_mark(terms, m->hyps[i].rigid_head);
    }
    for (size_t i = 0; i < m->choice_count; ++i) {
        if (!m->choices[i].kind) continue;
        ht_collect_mark(terms, m->choices[i].search.goal);
        ht_collect_mark(terms, m->choices[i].search.head);
        ht_collect_mark(terms, m->choices[i].search.frame.goal);
    }
}

static size_t moved(const size_t *forward, size_t at)
{
    return at == NONE ? NONE : forward[at];
}

static void collect_relocate(const HTCollection *terms, void *context)
{
    Collection *c = context;
    HolV2Machine *m = c->machine;
    for (size_t i = 0; i < m->query_count; ++i) m->query[i] = ht_collect_term(terms, m->query[i]);
    for (size_t i = 0; i < m->work_count; ++i) {
        if (!c->frames[i]) continue;
        Frame frame = m->work[i];
        frame.goal = ht_collect_term(terms, frame.goal);
        frame.next = moved(c->frame_forward, frame.next);
        frame.hyps = moved(c->hyp_forward, frame.hyps);
        m->work[c->frame_forward[i]] = frame;
    }
    for (size_t i = 0; i < m->hyp_count; ++i) {
        if (!c->hyps[i]) continue;
        Hypothesis hyp = m->hyps[i];
        hyp.fact = ht_collect_term(terms, hyp.fact);
        hyp.rigid_head = hyp.rigid_head == HT_NONE ? HT_NONE : ht_collect_term(terms, hyp.rigid_head);
        hyp.next = moved(c->hyp_forward, hyp.next);
        m->hyps[c->hyp_forward[i]] = hyp;
    }
    for (size_t i = 0; i < m->choice_count; ++i) {
        Choice *choice = &m->choices[i];
        choice->checkpoint.terms.heap = ht_collect_heap(terms, choice->checkpoint.terms.heap);
        choice->checkpoint.terms.trail = ht_collect_trail(terms, choice->checkpoint.terms.trail);
        choice->checkpoint.work = c->frame_forward[choice->checkpoint.work];
        choice->checkpoint.hyps = c->hyp_forward[choice->checkpoint.hyps];
        if (!choice->kind) {
            choice->work_head = moved(c->frame_forward, choice->work_head);
            continue;
        }
        choice->search.goal = ht_collect_term(terms, choice->search.goal);
        choice->search.head = ht_collect_term(terms, choice->search.head);
        choice->search.local = moved(c->hyp_forward, choice->search.local);
        choice->search.frame.goal = ht_collect_term(terms, choice->search.frame.goal);
        choice->search.frame.next = moved(c->frame_forward, choice->search.frame.next);
        choice->search.frame.hyps = moved(c->hyp_forward, choice->search.frame.hyps);
    }
    m->work_head = moved(c->frame_forward, m->work_head);
    m->work_count = c->frame_forward[m->work_count];
    m->hyp_count = c->hyp_forward[m->hyp_count];
}

/* Between two goals nothing but the continuations, the choice points, the
    * disagreements and the identities known to the host can reach a term: the
    * goal executed last is dead. Compaction keeps the order of terms, frames
    * and hypotheses, so every checkpoint remains a prefix of the same state. */
static void collect(HolV2Machine *m)
{
    static const HTCollector collector = { collect_mark, collect_relocate };
    Collection c = { m, NULL, NULL, NULL, NULL };
    c.frames = calloc(m->work_count + 1, 1);
    c.hyps = calloc(m->hyp_count + 1, 1);
    c.frame_forward = m->work_count < SIZE_MAX / sizeof(size_t) ? malloc((m->work_count + 1) * sizeof(size_t)) : NULL;
    c.hyp_forward = m->hyp_count < SIZE_MAX / sizeof(size_t) ? malloc((m->hyp_count + 1) * sizeof(size_t)) : NULL;
    int collected = 0;
    if (c.frames && c.hyps && c.frame_forward && c.hyp_forward) {
        keep_frames(&c, m->work_head);
        for (size_t i = 0; i < m->choice_count; ++i) {
            Choice *choice = &m->choices[i];
            if (!choice->kind) {
                keep_frames(&c, choice->work_head);
                continue;
            }
            keep_frames(&c, choice->search.frame.next);
            keep_hyps(&c, choice->search.frame.hyps);
            keep_hyps(&c, choice->search.local);
        }
        size_t frames = 0, hyps = 0;
        for (size_t i = 0; i < m->work_count; ++i) { c.frame_forward[i] = frames; frames += c.frames[i]; }
        for (size_t i = 0; i < m->hyp_count; ++i) { c.hyp_forward[i] = hyps; hyps += c.hyps[i]; }
        c.frame_forward[m->work_count] = frames;
        c.hyp_forward[m->hyp_count] = hyps;
        collected = ht_collect(m->terms, m->permanent, &collector, &c);
    }
    free(c.frames);
    free(c.hyps);
    free(c.frame_forward);
    free(c.hyp_forward);
    if (collected) ++m->collections;
    size_t heap = ht_heap_count(m->terms), growth = heap - m->permanent;
    if (growth < m->collect_step) growth = m->collect_step;
    m->collect_at = !m->collect_step ? 0 : heap > SIZE_MAX - growth ? SIZE_MAX : heap + growth;
}

void hol_v2_set_collection_step(HolV2Machine *m, size_t nodes)
{
    if (!m) return;
    m->collect_step = nodes;
    size_t heap = ht_heap_count(m->terms);
    m->collect_at = !nodes ? 0 : heap > SIZE_MAX - nodes ? SIZE_MAX : heap + nodes;
}

size_t hol_v2_heap_count(const HolV2Machine *m)
{
    return m ? ht_heap_count(m->terms) : 0;
}

size_t hol_v2_collections(const HolV2Machine *m)
{
    return m ? m->collections : 0;
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
    for (m->batch = 0; m->batch < BATCH; ++m->batch) {
        if (m->action == ACTION_FAIL) {
            if (!backtrack_step(m)) return m->error[0] ? -1 : 0;
            if (m->event_kind) return 3;
        }
        if (m->action == ACTION_SEARCH) {
            if (!search_step(m)) {
                if (m->error[0]) return -1;
                m->action = ACTION_FAIL;
            }
            if (m->event_kind) return 3;
            continue;
        }
        if (m->action == ACTION_FAIL) continue;
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
        if (ht_heap_count(m->terms) >= m->collect_at) collect(m);
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
    size_t heap = ht_heap_count(m->terms), first = ht_sealed(m->terms), variables = 0;
    for (size_t i = first; i < heap; ++i) if (ht_view(m->terms, i).tag == HT_VAR) ++variables;
    if (!push_word(m, (int64_t) variables)) return 0;
    for (size_t i = first; i < heap; ++i) {
        HTView variable = ht_view(m->terms, i);
        if (variable.tag != HT_VAR) continue;
        ht_pin(m->terms, i);
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

size_t hol_v2_root_state_size(HolV2Machine *m, int with_query)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    size_t variables = with_query ? m->query_count : 0;
    if (!push_word(m, (int64_t) variables)) return 0;
    for (size_t i = 0; i < variables; ++i) {
        HTView variable = ht_view(m->terms, m->query[i]);
        if (!push_word(m, HT_VAR) || !push_word(m, (int64_t) variable.uid)
            || !push_word(m, (int64_t) variable.scope) || !push_word(m, variable.is_type)
            || !push_word(m, variable.meta) || !push_term(m, m->query[i])) return 0;
    }
    size_t pending = ht_pending_count(m->terms);
    if (!push_word(m, (int64_t) pending)) return 0;
    for (size_t i = 0; i < pending; ++i) {
        HTerm left, right;
        if (!ht_pending(m->terms, i, &left, &right) || !push_term(m, left) || !push_term(m, right)) return 0;
    }
    return m->buffer_count;
}

size_t hol_v2_pending_count(const HolV2Machine *m)
{
    return m && !m->error[0] ? ht_pending_count(m->terms) : 0;
}

uint64_t hol_v2_uid_frontier(const HolV2Machine *m)
{
    return m && m->terms ? ht_next_uid(m->terms) : 0;
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

static int term_declarations(HolV2Machine *m, HTerm term, size_t *count)
{
    int64_t *wire = NULL;
    size_t length = 0;
    if (!ht_export(m->terms, term, &wire, &length)) return fail(m, ht_error(m->terms));
    int success = 1;
    for (size_t at = 0; success && at < length;) {
        size_t start = at++;
        int64_t tag = wire[start];
        size_t payload = tag == HT_VAR ? 4 : tag == HT_NOMINAL ? 3 : tag == HT_CONST ? 2 : tag == HT_WILD ? 0 : 1;
        if (payload > length - at) { success = fail(m, "Truncated V2 declaration source"); break; }
        if (tag == HT_VAR || tag == HT_NOMINAL) {
            ++*count;
            for (size_t i = start; success && i < at + payload; ++i) success = push_word(m, wire[i]);
        } else if (tag == HT_NAT) {
            if (wire[at] < 0 || (uint64_t) wire[at] > length - at - 1) { success = fail(m, "Invalid V2 declaration natural"); break; }
            payload += (size_t) wire[at];
        } else if (tag != HT_CONST && tag != HT_APP && tag != HT_INDEX && tag != HT_LAM && tag != HT_WILD) {
            success = fail(m, "Invalid V2 declaration source tag");
            break;
        }
        at += payload;
    }
    free(wire);
    return success;
}

size_t hol_v2_declarations_size(HolV2Machine *m)
{
    if (!m || m->error[0]) return 0;
    m->buffer_count = 0;
    size_t count = 0;
    int success = push_word(m, 0);
    for (size_t at = m->work_head; success && at != NONE; at = m->work[at].next) {
        Frame frame = m->work[at];
        for (size_t h = frame.hyps; success && h != NONE; h = m->hyps[h].next) {
            success = term_declarations(m, m->hyps[h].fact, &count);
        }
        if (success) success = term_declarations(m, frame.goal, &count);
    }
    if (!success) return 0;
    m->buffer[0] = (int64_t) count;
    return m->buffer_count;
}

int hol_v2_declarations(HolV2Machine *m, int64_t *output, size_t capacity)
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
            success = begin_search(m, result, NULL);
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
    if (operation < HV2_ORDINARY || operation > HV2_NATURAL || symbol >= INT64_MAX || symbol >= SIZE_MAX / sizeof(*m->roles)) return fail(m, "Invalid V2 dynamic symbol") ? 1 : -1;
    if (symbol < m->symbol_count) {
        if (m->roles[symbol] != operation) { fail(m, "V2 dynamic symbol role conflict"); return -1; }
        if (operation == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, symbol)) { fail(m, ht_error(m->terms)); return -1; }
        if (operation == HV2_ARITHMETIC && !ht_set_arithmetic_symbol(m->terms, symbol)) { fail(m, ht_error(m->terms)); return -1; }
        return 1;
    }
    int64_t *roles = realloc(m->roles, (symbol + 1) * sizeof(*m->roles));
    if (!roles) { fail(m, "V2 dynamic symbol allocation failed"); return -1; }
    m->roles = roles;
    while (m->symbol_count <= symbol) m->roles[m->symbol_count++] = HV2_ORDINARY;
    m->roles[symbol] = operation;
    if (operation == HV2_SUCCESSOR) ht_set_successor(m->terms, symbol);
    if (operation == HV2_PRESBURGER && !ht_set_opaque_symbol(m->terms, symbol)) { fail(m, ht_error(m->terms)); return -1; }
    if (operation == HV2_ARITHMETIC && !ht_set_arithmetic_symbol(m->terms, symbol)) { fail(m, ht_error(m->terms)); return -1; }
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
    free(m->predicates);
    free(m->buckets);
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
    copy->predicates = copy_array(source->predicates, source->predicate_count, sizeof(*source->predicates));
    copy->buckets = copy_array(source->buckets, source->bucket_capacity, sizeof(*source->buckets));
    copy->query = copy_array(source->query, source->query_count, sizeof(*source->query));
    copy->work = copy_array(source->work, source->work_count, sizeof(*source->work));
    copy->hyps = copy_array(source->hyps, source->hyp_count, sizeof(*source->hyps));
    copy->choices = copy_array(source->choices, source->choice_count, sizeof(*source->choices));
    copy->buffer = copy_array(source->buffer, source->buffer_count, sizeof(*source->buffer));
    copy->fact_capacity = copy->fact_count;
    copy->work_capacity = copy->work_count;
    copy->hyp_capacity = copy->hyp_count;
    copy->choice_capacity = copy->choice_count;
    copy->buffer_capacity = copy->buffer_count;
    if (!copy->terms || (source->assignment_count && !copy->assignments) || (copy->symbol_count && !copy->roles) || (copy->fact_count && !copy->facts)
        || (copy->predicate_count && !copy->predicates) || (copy->bucket_capacity && !copy->buckets)
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
        ht_pin(m->terms, target);
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

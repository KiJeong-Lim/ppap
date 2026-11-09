#include "term.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define UID_EMPTY UINT64_MAX
#define TERM_DEPTH_LIMIT 8192

typedef struct {
    int tag, is_type;
    HTerm a, b;
    uint64_t uid;
    size_t scope;
    int64_t meta;
    char *digits;
} TermNode;

typedef struct { HTerm variable, binding; size_t scope; } Trail;
typedef struct { HTerm left, right; size_t next; } Pending;
typedef struct { uint64_t uid; HTerm term; } Identity;

struct HolTermStore {
    TermNode *nodes;
    size_t count, capacity;
    Trail *trail;
    size_t trail_count, trail_capacity;
    Pending *pending;
    size_t pending_count, pending_capacity, pending_head;
    Identity *identities;
    size_t identity_capacity, identity_count;
    uint64_t next_uid;
    size_t successor;
    unsigned char *opaque;
    size_t opaque_count, opaque_capacity;
    uint64_t work, work_limit;
    size_t operations;
    uint64_t changes;
    char error[192];
};

typedef struct { HTerm *items; size_t count, capacity; } Terms;
typedef struct { int64_t *items; size_t count, capacity; } Words;

static int fail(HolTermStore *s, const char *message)
{
    if (s && !s->error[0]) {
        size_t length = strlen(message);
        if (length >= sizeof(s->error)) {
            length = sizeof(s->error) - 1;
        }
        memcpy(s->error, message, length);
        s->error[length] = '\0';
    }
    return 0;
}

static int reserve(HolTermStore *s, void **pointer, size_t *capacity, size_t count, size_t width)
{
    if (count <= *capacity) {
        return 1;
    }
    if (!width || count > SIZE_MAX / width) {
        return fail(s, "Term allocation size overflow");
    }
    size_t next = *capacity ? *capacity : 32;
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
    void *resized = realloc(*pointer, next * width);
    if (!resized) {
        return fail(s, "Term allocation failed");
    }
    *pointer = resized;
    *capacity = next;
    return 1;
}

static int push_term(HolTermStore *s, Terms *terms, HTerm term)
{
    if (term == HT_NONE || terms->count == SIZE_MAX || !reserve(s, (void **) &terms->items, &terms->capacity, terms->count + 1, sizeof(*terms->items))) {
        return 0;
    }
    terms->items[terms->count++] = term;
    return 1;
}

static int push_word(HolTermStore *s, Words *words, int64_t word)
{
    if (words->count == SIZE_MAX || !reserve(s, (void **) &words->items, &words->capacity, words->count + 1, sizeof(*words->items))) {
        return 0;
    }
    words->items[words->count++] = word;
    return 1;
}

static HTerm node(HolTermStore *s, TermNode value)
{
    if (!s || s->error[0] || s->count >= INT64_MAX || !reserve(s, (void **) &s->nodes, &s->capacity, s->count + 1, sizeof(*s->nodes))) {
        return HT_NONE;
    }
    HTerm result = s->count++;
    s->nodes[result] = value;
    return result;
}

static size_t bucket(uint64_t uid, size_t capacity)
{
    return (size_t) (uid * UINT64_C(11400714819323198485)) & (capacity - 1);
}

static int reserve_identities(HolTermStore *s)
{
    if (s->identity_capacity && s->identity_count < s->identity_capacity / 2) {
        return 1;
    }
    size_t capacity = s->identity_capacity ? s->identity_capacity * 2 : 64;
    if (capacity < s->identity_capacity || capacity > SIZE_MAX / sizeof(Identity)) {
        return fail(s, "Term identity table overflow");
    }
    Identity *table = malloc(capacity * sizeof(*table));
    if (!table) {
        return fail(s, "Term identity allocation failed");
    }
    for (size_t i = 0; i < capacity; ++i) {
        table[i] = (Identity) { UID_EMPTY, HT_NONE };
    }
    for (size_t i = 0; i < s->identity_capacity; ++i) {
        Identity entry = s->identities[i];
        if (entry.uid == UID_EMPTY) {
            continue;
        }
        size_t index = bucket(entry.uid, capacity);
        while (table[index].uid != UID_EMPTY) {
            index = (index + 1) & (capacity - 1);
        }
        table[index] = entry;
    }
    free(s->identities);
    s->identities = table;
    s->identity_capacity = capacity;
    return 1;
}

static int insert_identity(HolTermStore *s, uint64_t uid, HTerm term, int restoring)
{
    if (!reserve_identities(s)) {
        return 0;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            if (restoring && s->identities[index].term == HT_NONE) {
                s->identities[index].term = term;
                return 1;
            }
            return fail(s, "Duplicate term identity");
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
    s->identities[index] = (Identity) { uid, term };
    ++s->identity_count;
    return 1;
}

static void remove_identity(HolTermStore *s, uint64_t uid)
{
    if (!s->identity_capacity) {
        return;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            s->identities[index].term = HT_NONE;
            return;
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
}

HolTermStore *ht_create(void)
{
    HolTermStore *s = calloc(1, sizeof(*s));
    if (s) {
        s->successor = HT_NONE;
        s->pending_head = HT_NONE;
        s->work_limit = UINT64_C(5000000);
    }
    return s;
}

void ht_destroy(HolTermStore *s)
{
    if (!s) {
        return;
    }
    for (size_t i = 0; i < s->count; ++i) {
        free(s->nodes[i].digits);
    }
    free(s->nodes);
    free(s->trail);
    free(s->pending);
    free(s->identities);
    free(s->opaque);
    free(s);
}

const char *ht_error(const HolTermStore *s)
{
    return s ? s->error : "Term store allocation failed";
}

size_t ht_heap_count(const HolTermStore *s)
{
    return s ? s->count : 0;
}

HTCheckpoint ht_checkpoint(const HolTermStore *s)
{
    return (HTCheckpoint) { s->count, s->trail_count, s->pending_count, s->pending_head };
}

int ht_restore(HolTermStore *s, HTCheckpoint saved)
{
    if (!s || saved.heap > s->count || saved.trail > s->trail_count || saved.pending > s->pending_count || (saved.pending_head != HT_NONE && saved.pending_head >= saved.pending)) {
        return fail(s, "Invalid term checkpoint");
    }
    while (s->trail_count > saved.trail) {
        Trail old = s->trail[--s->trail_count];
        s->nodes[old.variable].a = old.binding;
        s->nodes[old.variable].scope = old.scope;
    }
    while (s->count > saved.heap) {
        TermNode old = s->nodes[--s->count];
        if (old.tag == HT_VAR || old.tag == HT_NOMINAL) {
            remove_identity(s, old.uid);
        }
        free(old.digits);
    }
    s->pending_count = saved.pending;
    s->pending_head = saved.pending_head;
    return 1;
}

uint64_t ht_next_uid(const HolTermStore *s)
{
    return s->next_uid;
}

int ht_advance_uid(HolTermStore *s, uint64_t next_uid)
{
    if (next_uid > INT64_MAX) {
        return fail(s, "Term identity overflow");
    }
    if (s->next_uid < next_uid) {
        s->next_uid = next_uid;
    }
    return 1;
}

int ht_preserve_identity_history(HolTermStore *restored, const HolTermStore *live)
{
    if (!restored || !live || restored->error[0]) {
        return fail(restored, "Invalid term identity history");
    }
    if (restored == live) {
        return 1;
    }
    for (size_t i = 0; i < live->identity_capacity; ++i) {
        Identity entry = live->identities[i];
        if (entry.uid == UID_EMPTY) {
            continue;
        }
        int present = 0;
        if (restored->identity_capacity) {
            size_t index = bucket(entry.uid, restored->identity_capacity);
            while (restored->identities[index].uid != UID_EMPTY) {
                if (restored->identities[index].uid == entry.uid) {
                    present = 1;
                    break;
                }
                index = (index + 1) & (restored->identity_capacity - 1);
            }
        }
        if (!present && !insert_identity(restored, entry.uid, HT_NONE, 0)) {
            return 0;
        }
    }
    return ht_advance_uid(restored, live->next_uid);
}

void ht_set_successor(HolTermStore *s, size_t symbol)
{
    s->successor = symbol;
}

int ht_set_opaque_symbol(HolTermStore *s, size_t symbol)
{
    if (!s || s->error[0] || symbol >= INT64_MAX || symbol == SIZE_MAX) {
        return fail(s, "Invalid opaque symbol");
    }
    size_t count = symbol + 1;
    if (!reserve(s, (void **) &s->opaque, &s->opaque_capacity, count, sizeof(*s->opaque))) {
        return 0;
    }
    if (count > s->opaque_count) {
        memset(s->opaque + s->opaque_count, 0, count - s->opaque_count);
        s->opaque_count = count;
    }
    s->opaque[symbol] = 1;
    return 1;
}

int ht_set_work_limit(HolTermStore *s, uint64_t visits)
{
    if (!s || !visits) {
        return fail(s, "The native term work limit must be positive");
    }
    s->work_limit = visits;
    return 1;
}

uint64_t ht_work_limit(const HolTermStore *s)
{
    return s ? s->work_limit : 0;
}

static int operation_begin(HolTermStore *s)
{
    if (!s || s->error[0]) {
        return 0;
    }
    if (!s->operations) {
        s->work = 0;
    }
    if (s->operations == SIZE_MAX) {
        return fail(s, "Native term operation nesting overflow");
    }
    ++s->operations;
    return 1;
}

static void operation_end(HolTermStore *s)
{
    --s->operations;
}

static HTerm identity_node(HolTermStore *s, int tag, uint64_t uid, size_t scope, int is_type, int64_t meta, int restoring)
{
    if (uid >= INT64_MAX || scope > INT64_MAX || (is_type != 0 && is_type != 1) || meta < -1) {
        fail(s, "Invalid term identity metadata");
        return HT_NONE;
    }
    HTerm result = node(s, (TermNode) { tag, is_type, HT_NONE, HT_NONE, uid, scope, meta, NULL });
    if (result == HT_NONE || !insert_identity(s, uid, result, restoring)) {
        return HT_NONE;
    }
    if (s->next_uid <= uid) {
        s->next_uid = uid + 1;
    }
    return result;
}

HTerm ht_var(HolTermStore *s, size_t scope, int is_type, int64_t meta)
{
    return identity_node(s, HT_VAR, s->next_uid, scope, is_type, meta, 0);
}

HTerm ht_nominal(HolTermStore *s, size_t scope, int64_t meta)
{
    return identity_node(s, HT_NOMINAL, s->next_uid, scope, 0, meta, 0);
}

HTerm ht_constant(HolTermStore *s, size_t symbol, int64_t meta)
{
    if (symbol > INT64_MAX || meta < -1) {
        fail(s, "Invalid constant metadata");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_CONST, 0, symbol, HT_NONE, 0, 0, meta, NULL });
}

HTerm ht_nat(HolTermStore *s, const char *digits)
{
    if (!digits || !*digits) {
        fail(s, "Invalid natural literal");
        return HT_NONE;
    }
    for (const char *p = digits; *p; ++p) {
        if (*p < '0' || *p > '9') {
            fail(s, "Invalid natural literal");
            return HT_NONE;
        }
    }
    while (digits[0] == '0' && digits[1]) {
        ++digits;
    }
    size_t length = strlen(digits);
    char *copy = malloc(length + 1);
    if (!copy) {
        fail(s, "Natural literal allocation failed");
        return HT_NONE;
    }
    memcpy(copy, digits, length + 1);
    HTerm result = node(s, (TermNode) { HT_NAT, 0, HT_NONE, HT_NONE, 0, 0, -1, copy });
    if (result == HT_NONE) {
        free(copy);
    }
    return result;
}

static HTerm increment(HolTermStore *s, HTerm natural, int direction)
{
    const char *digits = s->nodes[natural].digits;
    size_t length = strlen(digits);
    char *work = malloc(length + 2);
    if (!work) {
        fail(s, "Natural arithmetic allocation failed");
        return HT_NONE;
    }
    memcpy(work + 1, digits, length + 1);
    size_t i = length;
    if (direction > 0) {
        while (i && work[i] == '9') {
            work[i--] = '0';
        }
        if (i) {
            ++work[i];
        } else {
            work[0] = '1';
        }
    } else {
        while (i && work[i] == '0') {
            work[i--] = '9';
        }
        if (!i) {
            free(work);
            fail(s, "Natural predecessor of zero");
            return HT_NONE;
        }
        --work[i];
    }
    HTerm result = ht_nat(s, i ? work + 1 : work);
    free(work);
    return result;
}

HTerm ht_index(HolTermStore *s, size_t index)
{
    if (index > INT64_MAX) {
        fail(s, "Bound variable index overflow");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_INDEX, 0, index, HT_NONE, 0, 0, -1, NULL });
}

HTerm ht_lam(HolTermStore *s, HTerm body, int64_t meta)
{
    if (body >= s->count || meta < -1) {
        fail(s, "Invalid lambda term");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_LAM, 0, body, HT_NONE, 0, 0, meta, NULL });
}

HTerm ht_app(HolTermStore *s, HTerm function, HTerm argument, int64_t meta)
{
    if (function >= s->count || argument >= s->count || meta < -1) {
        fail(s, "Invalid application term");
        return HT_NONE;
    }
    HTerm f = ht_deref(s, function);
    HTerm a = ht_deref(s, argument);
    if (s->nodes[f].tag == HT_CONST && s->nodes[f].a == s->successor && s->nodes[a].tag == HT_NAT) {
        return increment(s, a, 1);
    }
    return node(s, (TermNode) { HT_APP, 0, function, argument, 0, 0, meta, NULL });
}

HTerm ht_wildcard(HolTermStore *s)
{
    return node(s, (TermNode) { HT_WILD, 0, HT_NONE, HT_NONE, 0, 0, -1, NULL });
}

HTerm ht_lookup_uid(const HolTermStore *s, uint64_t uid)
{
    if (!s->identity_capacity) {
        return HT_NONE;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            return s->identities[index].term;
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
    return HT_NONE;
}

HTerm ht_deref(const HolTermStore *s, HTerm term)
{
    if (!s || term >= s->count) {
        return HT_NONE;
    }
    while (s->nodes[term].tag == HT_VAR && s->nodes[term].a != HT_NONE) {
        term = s->nodes[term].a;
    }
    return term;
}

HTView ht_view(const HolTermStore *s, HTerm term)
{
    if (!s || term >= s->count) {
        return (HTView) { -1, HT_NONE, HT_NONE, 0, 0, 0, 0, -1, NULL };
    }
    TermNode n = s->nodes[term];
    return (HTView) { n.tag, n.a, n.b, n.uid, n.a, n.scope, n.is_type, n.meta, n.digits };
}

static int depth_okay(HolTermStore *s, size_t depth)
{
    if (s->work >= s->work_limit) {
        return fail(s, "Native term work limit exceeded");
    }
    ++s->work;
    return depth < TERM_DEPTH_LIMIT || fail(s, "Term nesting exceeds the native work stack");
}

static HTerm shift(HolTermStore *s, HTerm term, size_t amount, size_t cutoff, size_t depth)
{
    if (!depth_okay(s, depth) || term == HT_NONE) {
        return HT_NONE;
    }
    term = ht_deref(s, term);
    TermNode n = s->nodes[term];
    if (!amount) {
        return term;
    }
    if (n.tag == HT_INDEX && n.a >= cutoff) {
        if (n.a > INT64_MAX - amount) {
            fail(s, "Bound variable shift overflow");
            return HT_NONE;
        }
        return ht_index(s, n.a + amount);
    }
    if (n.tag == HT_APP) {
        HTerm left = shift(s, n.a, amount, cutoff, depth + 1);
        HTerm right = shift(s, n.b, amount, cutoff, depth + 1);
        return left == n.a && right == n.b ? term : ht_app(s, left, right, n.meta);
    }
    if (n.tag == HT_LAM) {
        HTerm body = shift(s, n.a, amount, cutoff + 1, depth + 1);
        return body == n.a ? term : ht_lam(s, body, n.meta);
    }
    return term;
}

static HTerm substitute(HolTermStore *s, HTerm term, HTerm argument, size_t binder, size_t depth)
{
    if (!depth_okay(s, depth) || term == HT_NONE || argument == HT_NONE) {
        return HT_NONE;
    }
    term = ht_deref(s, term);
    TermNode n = s->nodes[term];
    if (n.tag == HT_INDEX) {
        if (n.a == binder) {
            return shift(s, argument, binder, 0, depth + 1);
        }
        return n.a > binder ? ht_index(s, n.a - 1) : term;
    }
    if (n.tag == HT_APP) {
        HTerm left = substitute(s, n.a, argument, binder, depth + 1);
        HTerm right = substitute(s, n.b, argument, binder, depth + 1);
        return left == n.a && right == n.b ? term : ht_app(s, left, right, n.meta);
    }
    if (n.tag == HT_LAM) {
        HTerm body = substitute(s, n.a, argument, binder + 1, depth + 1);
        return body == n.a ? term : ht_lam(s, body, n.meta);
    }
    return term;
}

static HTerm normalize(HolTermStore *s, HTerm term, enum HTNormalForm form, size_t depth)
{
    if (!depth_okay(s, depth) || term == HT_NONE || s->error[0]) {
        return HT_NONE;
    }
    term = ht_deref(s, term);
    if (term == HT_NONE) {
        fail(s, "Invalid term reference");
        return HT_NONE;
    }
    TermNode n = s->nodes[term];
    if (n.tag == HT_APP) {
        HTerm function = normalize(s, n.a, HT_WHNF, depth + 1);
        if (function == HT_NONE) {
            return HT_NONE;
        }
        TermNode f = s->nodes[function];
        if (f.tag == HT_LAM) {
            HTerm body = substitute(s, f.a, n.b, 0, depth + 1);
            return normalize(s, body, form, depth + 1);
        }
        if (form != HT_WHNF) {
            function = normalize(s, function, form, depth + 1);
        }
        HTerm argument = form == HT_NF ? normalize(s, n.b, HT_NF, depth + 1) : n.b;
        if (function == n.a && argument == n.b) {
            HTerm arg = ht_deref(s, argument);
            if (arg == HT_NONE || s->nodes[function].tag != HT_CONST || s->nodes[function].a != s->successor || s->nodes[arg].tag != HT_NAT) {
                return term;
            }
        }
        return ht_app(s, function, argument, n.meta);
    }
    if (n.tag == HT_LAM && form != HT_WHNF) {
        HTerm body = normalize(s, n.a, form, depth + 1);
        return body == n.a ? term : ht_lam(s, body, n.meta);
    }
    return term;
}

HTerm ht_normalize(HolTermStore *s, HTerm term, enum HTNormalForm form)
{
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTerm result = normalize(s, term, form, 0);
    operation_end(s);
    return result;
}

HTerm ht_apply(HolTermStore *s, HTerm function, HTerm argument)
{
    return ht_normalize(s, ht_app(s, function, argument, -1), HT_HNF);
}

static int spine_view(HolTermStore *s, HTerm term, HTSpine *spine)
{
    *spine = (HTSpine) { HT_NONE, NULL, 0 };
    Terms arguments = { 0 };
    term = ht_deref(s, term);
    while (term != HT_NONE && s->nodes[term].tag == HT_APP) {
        if (!depth_okay(s, 0)) {
            free(arguments.items);
            return 0;
        }
        TermNode n = s->nodes[term];
        if (!push_term(s, &arguments, n.b)) {
            free(arguments.items);
            return 0;
        }
        term = ht_deref(s, n.a);
    }
    if (term == HT_NONE) {
        free(arguments.items);
        return fail(s, "Invalid term spine");
    }
    if (s->nodes[term].tag == HT_NAT && strcmp(s->nodes[term].digits, "0")) {
        if (s->successor == HT_NONE) {
            free(arguments.items);
            return fail(s, "Natural successor symbol is not configured");
        }
        HTerm predecessor = increment(s, term, -1);
        if (!push_term(s, &arguments, predecessor)) {
            free(arguments.items);
            return 0;
        }
        term = ht_constant(s, s->successor, -1);
    }
    for (size_t i = 0; i < arguments.count / 2; ++i) {
        HTerm swap = arguments.items[i];
        arguments.items[i] = arguments.items[arguments.count - i - 1];
        arguments.items[arguments.count - i - 1] = swap;
    }
    *spine = (HTSpine) { term, arguments.items, arguments.count };
    return term != HT_NONE;
}

int ht_spine(HolTermStore *s, HTerm term, HTSpine *spine)
{
    *spine = (HTSpine) { HT_NONE, NULL, 0 };
    if (!operation_begin(s)) {
        return 0;
    }
    int result = spine_view(s, term, spine);
    operation_end(s);
    return result;
}

void ht_spine_free(HTSpine *spine)
{
    free(spine->args);
    *spine = (HTSpine) { HT_NONE, NULL, 0 };
}

static int equal(HolTermStore *s, HTerm left, HTerm right, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return 0;
    }
    left = ht_deref(s, left);
    right = ht_deref(s, right);
    if (left == right) {
        return 1;
    }
    TermNode a = s->nodes[left], b = s->nodes[right];
    if (a.tag != b.tag) {
        return 0;
    }
    switch (a.tag) {
        case HT_VAR:
        case HT_NOMINAL:
            return a.uid == b.uid;
        case HT_CONST:
        case HT_INDEX:
            return a.a == b.a;
        case HT_NAT:
            return !strcmp(a.digits, b.digits);
        case HT_WILD:
            return 1;
        case HT_APP:
            return equal(s, a.a, b.a, depth + 1) && equal(s, a.b, b.b, depth + 1);
        case HT_LAM:
            return equal(s, a.a, b.a, depth + 1);
        default:
            return 0;
    }
}

static int rigid(HolTermStore *s, HTerm term)
{
    TermNode n = s->nodes[ht_deref(s, term)];
    if (n.tag == HT_CONST && n.a < s->opaque_count && s->opaque[n.a]) {
        return 0;
    }
    return n.tag == HT_CONST || n.tag == HT_NOMINAL || n.tag == HT_INDEX || n.tag == HT_NAT;
}

static int is_constant(HolTermStore *s, HTerm term)
{
    int tag = s->nodes[ht_deref(s, term)].tag;
    return tag == HT_CONST || tag == HT_NOMINAL || tag == HT_NAT;
}

static size_t level(HolTermStore *s, HTerm term)
{
    return s->nodes[ht_deref(s, term)].scope;
}

static size_t position(HolTermStore *s, HTerm term, const HTerm *terms, size_t count)
{
    for (size_t i = 0; i < count; ++i) {
        if (equal(s, term, terms[i], 0)) {
            return i;
        }
    }
    return SIZE_MAX;
}

static int pattern(HolTermStore *s, HTerm variable, const HTerm *arguments, size_t count)
{
    size_t scope = level(s, variable);
    for (size_t i = 0; i < count; ++i) {
        if (!rigid(s, arguments[i]) || (is_constant(s, arguments[i]) && level(s, arguments[i]) <= scope) || position(s, arguments[i], arguments, i) != SIZE_MAX) {
            return 0;
        }
    }
    return 1;
}

static int trail_variable(HolTermStore *s, HTerm variable)
{
    if (!reserve(s, (void **) &s->trail, &s->trail_capacity, s->trail_count + 1, sizeof(*s->trail))) {
        return 0;
    }
    TermNode n = s->nodes[variable];
    s->trail[s->trail_count++] = (Trail) { variable, n.a, n.scope };
    return 1;
}

static int occurs(HolTermStore *s, HTerm variable, HTerm term, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return 1;
    }
    term = ht_deref(s, term);
    if (term == variable) {
        return 1;
    }
    TermNode n = s->nodes[term];
    if (n.tag == HT_APP) {
        return occurs(s, variable, n.a, depth + 1) || occurs(s, variable, n.b, depth + 1);
    }
    return n.tag == HT_LAM && occurs(s, variable, n.a, depth + 1);
}

static int lower_scopes(HolTermStore *s, HTerm term, size_t scope, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return 0;
    }
    term = ht_deref(s, term);
    TermNode n = s->nodes[term];
    if (n.tag == HT_VAR && n.scope > scope) {
        if (!trail_variable(s, term)) {
            return 0;
        }
        s->nodes[term].scope = scope;
    } else if (n.tag == HT_APP) {
        return lower_scopes(s, n.a, scope, depth + 1) && lower_scopes(s, n.b, scope, depth + 1);
    } else if (n.tag == HT_LAM) {
        return lower_scopes(s, n.a, scope, depth + 1);
    }
    return 1;
}

static int index_free(HolTermStore *s, HTerm term, size_t index, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return 1;
    }
    term = ht_deref(s, term);
    TermNode n = s->nodes[term];
    if (n.tag == HT_INDEX) {
        return n.a == index;
    }
    if (n.tag == HT_APP) {
        return index_free(s, n.a, index, depth + 1) || index_free(s, n.b, index, depth + 1);
    }
    return n.tag == HT_LAM && index_free(s, n.a, index + 1, depth + 1);
}

static HTerm remove_binder(HolTermStore *s, HTerm term, size_t index, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return HT_NONE;
    }
    term = ht_deref(s, term);
    TermNode n = s->nodes[term];
    if (n.tag == HT_INDEX && n.a > index) {
        return ht_index(s, n.a - 1);
    }
    if (n.tag == HT_APP) {
        HTerm a = remove_binder(s, n.a, index, depth + 1);
        HTerm b = remove_binder(s, n.b, index, depth + 1);
        return a == n.a && b == n.b ? term : ht_app(s, a, b, n.meta);
    }
    if (n.tag == HT_LAM) {
        HTerm body = remove_binder(s, n.a, index + 1, depth + 1);
        return body == n.a ? term : ht_lam(s, body, n.meta);
    }
    return term;
}

static HTerm eta_reduce(HolTermStore *s, HTerm term, size_t depth)
{
    if (!depth_okay(s, depth) || term == HT_NONE) {
        return HT_NONE;
    }
    term = ht_deref(s, term);
    TermNode n = s->nodes[term];
    if (n.tag == HT_APP) {
        HTerm a = eta_reduce(s, n.a, depth + 1);
        HTerm b = eta_reduce(s, n.b, depth + 1);
        return a == n.a && b == n.b ? term : ht_app(s, a, b, n.meta);
    }
    if (n.tag == HT_LAM) {
        HTerm body = eta_reduce(s, n.a, depth + 1);
        if (body == HT_NONE) {
            return HT_NONE;
        }
        TermNode b = s->nodes[body];
        if (b.tag == HT_APP) {
            HTerm argument = ht_deref(s, b.b);
            if (s->nodes[argument].tag == HT_INDEX && s->nodes[argument].a == 0 && !index_free(s, b.a, 0, depth + 1)) {
                return eta_reduce(s, remove_binder(s, b.a, 0, depth + 1), depth + 1);
            }
        }
        return body == n.a ? term : ht_lam(s, body, n.meta);
    }
    return term;
}

static int assign(HolTermStore *s, HTerm variable, HTerm value)
{
    value = eta_reduce(s, ht_normalize(s, value, HT_NF), 0);
    if (value == HT_NONE) {
        return -1;
    }
    if (ht_deref(s, variable) == value) {
        return 1;
    }
    if (occurs(s, variable, value, 0)) {
        return s->error[0] ? -1 : 0;
    }
    if (!lower_scopes(s, value, s->nodes[variable].scope, 0) || !trail_variable(s, variable)) {
        return -1;
    }
    s->nodes[variable].a = value;
    ++s->changes;
    return 1;
}

static HTerm applications(HolTermStore *s, HTerm head, const HTerm *arguments, size_t count)
{
    for (size_t i = 0; i < count && head != HT_NONE; ++i) {
        head = ht_app(s, head, arguments[i], -1);
    }
    return head;
}

static HTerm abstractions(HolTermStore *s, HTerm body, const int64_t *hints, size_t count)
{
    while (count && body != HT_NONE) {
        body = ht_lam(s, body, hints[--count]);
    }
    return body;
}

static int64_t parameter_hint(HolTermStore *s, HTerm parameter, const Words *outer)
{
    TermNode n = s->nodes[ht_deref(s, parameter)];
    if (n.tag == HT_NOMINAL || n.tag == HT_VAR) {
        return n.meta;
    }
    if (n.tag == HT_INDEX && n.a < outer->count) {
        return outer->items[outer->count - n.a - 1];
    }
    return -1;
}

static int parameter_hints(HolTermStore *s, const HTerm *parameters, size_t count, const Words *outer, Words *hints)
{
    for (size_t i = 0; i < count; ++i) {
        if (!push_word(s, hints, parameter_hint(s, parameters[i], outer))) {
            return 0;
        }
    }
    return 1;
}

static int lhs_arguments(HolTermStore *s, const HTerm *parameters, size_t count, size_t binders, Terms *result)
{
    for (size_t i = 0; i < count; ++i) {
        if (!push_term(s, result, shift(s, parameters[i], binders, 0, 0))) {
            return 0;
        }
    }
    for (size_t i = binders; i > 0; --i) {
        if (!push_term(s, result, ht_index(s, i - 1))) {
            return 0;
        }
    }
    return 1;
}

static int atomic_order(HolTermStore *s, HTerm left, HTerm right)
{
    TermNode a = s->nodes[ht_deref(s, left)], b = s->nodes[ht_deref(s, right)];
    int rank_a = a.tag == HT_INDEX ? 1 : 0;
    int rank_b = b.tag == HT_INDEX ? 1 : 0;
    if (rank_a != rank_b) {
        return rank_a < rank_b ? -1 : 1;
    }
    if (a.tag == HT_INDEX && b.tag == HT_INDEX) {
        return a.a < b.a ? -1 : a.a > b.a;
    }
    if (a.tag == HT_NOMINAL && b.tag == HT_NOMINAL) {
        return a.uid < b.uid ? -1 : a.uid > b.uid;
    }
    if (a.tag != b.tag) {
        return a.tag < b.tag ? -1 : 1;
    }
    if (a.tag == HT_NAT) {
        size_t al = strlen(a.digits), bl = strlen(b.digits);
        return al == bl ? strcmp(a.digits, b.digits) : al < bl ? -1 : 1;
    }
    return a.a < b.a ? -1 : a.a > b.a;
}

static int common_arguments(HolTermStore *s, const Terms *left, const HTSpine *right, Terms *common)
{
    for (size_t i = 0; i < left->count; ++i) {
        if (position(s, left->items[i], right->args, right->count) != SIZE_MAX && !push_term(s, common, left->items[i])) {
            return 0;
        }
    }
    for (size_t i = 1; i < common->count; ++i) {
        HTerm value = common->items[i];
        size_t j = i;
        while (j && atomic_order(s, value, common->items[j - 1]) < 0) {
            common->items[j] = common->items[j - 1];
            --j;
        }
        common->items[j] = value;
    }
    return 1;
}

static int down(HolTermStore *s, const HTerm *selected, size_t count, const HTerm *arguments, size_t arity, Terms *result)
{
    for (size_t i = 0; i < count; ++i) {
        size_t index = position(s, selected[i], arguments, arity);
        if (index != SIZE_MAX && !push_term(s, result, ht_index(s, arity - index - 1))) {
            return 0;
        }
    }
    return 1;
}

static int visible_constants(HolTermStore *s, const HTerm *arguments, size_t count, size_t scope, Terms *result)
{
    for (size_t i = 0; i < count; ++i) {
        if (is_constant(s, arguments[i]) && level(s, arguments[i]) <= scope && !push_term(s, result, arguments[i])) {
            return 0;
        }
    }
    return 1;
}

/* 2 means that a non-pattern equation must be delayed. */
static int bind_value(HolTermStore *s, HTerm variable, HTerm value, const HTerm *parameters, size_t arity, const Words *outer, Words *bound, HTerm *result, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return -1;
    }
    value = ht_normalize(s, value, HT_HNF);
    if (value == HT_NONE) {
        return -1;
    }
    TermNode n = s->nodes[value];
    if (n.tag == HT_LAM) {
        if (!push_word(s, bound, n.meta)) {
            return -1;
        }
        HTerm body = HT_NONE;
        int status = bind_value(s, variable, n.a, parameters, arity, outer, bound, &body, depth + 1);
        --bound->count;
        if (status == 1) {
            *result = ht_lam(s, body, n.meta);
            return *result == HT_NONE ? -1 : 1;
        }
        return status;
    }
    if (n.tag == HT_NAT) {
        *result = value;
        return 1;
    }
    HTSpine rhs = { 0 };
    Terms lhs = { 0 }, common = { 0 }, lhs_args = { 0 }, rhs_args = { 0 };
    Words hints = { 0 }, rhs_hints = { 0 };
    int status = -1;
    if (!ht_spine(s, value, &rhs) || !lhs_arguments(s, parameters, arity, bound->count, &lhs)) {
        goto finish;
    }
    HTerm head = ht_deref(s, rhs.head);
    TermNode h = s->nodes[head];
    if (h.tag == HT_WILD) {
        *result = ht_var(s, s->nodes[variable].scope, s->nodes[variable].is_type, -1);
        status = *result == HT_NONE ? -1 : 1;
        goto finish;
    }
    if (rigid(s, head)) {
        HTerm output_head = HT_NONE;
        if (is_constant(s, head) && level(s, head) <= s->nodes[variable].scope) {
            output_head = head;
        } else {
            size_t index = position(s, head, lhs.items, lhs.count);
            if (index == SIZE_MAX) {
                status = 0;
                goto finish;
            }
            output_head = ht_index(s, lhs.count - index - 1);
        }
        for (size_t i = 0; i < rhs.count; ++i) {
            HTerm argument;
            status = bind_value(s, variable, rhs.args[i], parameters, arity, outer, bound, &argument, depth + 1);
            if (status != 1 || !push_term(s, &lhs_args, argument)) {
                if (s->error[0]) {
                    status = -1;
                }
                goto finish;
            }
        }
        *result = applications(s, output_head, lhs_args.items, lhs_args.count);
        status = *result == HT_NONE ? -1 : 1;
        goto finish;
    }
    if (h.tag != HT_VAR || head == variable) {
        status = 0;
        goto finish;
    }
    for (size_t i = 0; i < rhs.count; ++i) {
        rhs.args[i] = ht_normalize(s, rhs.args[i], HT_NF);
        if (rhs.args[i] == HT_NONE) {
            goto finish;
        }
    }
    if (!common_arguments(s, &lhs, &rhs, &common)) {
        goto finish;
    }
    for (size_t i = 0; i < outer->count; ++i) {
        if (!push_word(s, &hints, outer->items[i])) {
            goto finish;
        }
    }
    for (size_t i = 0; i < bound->count; ++i) {
        if (!push_word(s, &hints, bound->items[i])) {
            goto finish;
        }
    }
    if (!parameter_hints(s, rhs.args, rhs.count, &hints, &rhs_hints)) {
        goto finish;
    }
    size_t left_scope = s->nodes[variable].scope, right_scope = h.scope;
    if (pattern(s, head, rhs.args, rhs.count)) {
        if (left_scope < right_scope) {
            if (!visible_constants(s, lhs.items, lhs.count, right_scope, &rhs_args) || !down(s, rhs_args.items, rhs_args.count, lhs.items, lhs.count, &lhs_args)) {
                goto finish;
            }
        } else {
            if (!visible_constants(s, rhs.args, rhs.count, left_scope, &lhs_args) || !down(s, lhs_args.items, lhs_args.count, rhs.args, rhs.count, &rhs_args)) {
                goto finish;
            }
        }
        if (!down(s, common.items, common.count, lhs.items, lhs.count, &lhs_args) || !down(s, common.items, common.count, rhs.args, rhs.count, &rhs_args)) {
            goto finish;
        }
    } else {
        int beta_pattern = left_scope >= right_scope;
        for (size_t i = 0; i < rhs.count; ++i) {
            if (!rigid(s, rhs.args[i]) || (is_constant(s, rhs.args[i]) && level(s, rhs.args[i]) <= right_scope)) {
                beta_pattern = 0;
            }
        }
        if (!beta_pattern) {
            status = 2;
            goto finish;
        }
        for (size_t i = 0; i < rhs.count; ++i) {
            HTerm argument = rhs.args[i];
            int visible = is_constant(s, argument) && level(s, argument) <= left_scope;
            size_t index = position(s, argument, lhs.items, lhs.count);
            if (visible || index != SIZE_MAX) {
                if (!push_term(s, &rhs_args, ht_index(s, rhs.count - i - 1)) || !push_term(s, &lhs_args, visible ? argument : ht_index(s, lhs.count - index - 1))) {
                    goto finish;
                }
            }
        }
    }
    HTerm common_head = ht_var(s, left_scope, s->nodes[variable].is_type || h.is_type, -1);
    HTerm right_body = applications(s, common_head, rhs_args.items, rhs_args.count);
    HTerm replacement = abstractions(s, right_body, rhs_hints.items, rhs_hints.count);
    if (replacement == HT_NONE) {
        goto finish;
    }
    status = assign(s, head, replacement);
    if (status == 1) {
        *result = applications(s, common_head, lhs_args.items, lhs_args.count);
        if (*result == HT_NONE) {
            status = -1;
        }
    }
finish:
    ht_spine_free(&rhs);
    free(lhs.items);
    free(common.items);
    free(lhs_args.items);
    free(rhs_args.items);
    free(hints.items);
    free(rhs_hints.items);
    return s->error[0] ? -1 : status;
}

static int make_substitution(HolTermStore *s, HTerm variable, HTerm rhs, const HTerm *parameters, size_t arity, const Words *outer)
{
    HTCheckpoint checkpoint = ht_checkpoint(s);
    uint64_t changes = s->changes;
    Terms normalized = { 0 }, lhs = { 0 }, common = { 0 };
    Words lambda_hints = { 0 }, hints = { 0 }, bound = { 0 };
    HTSpine body_spine = { 0 };
    int status = -1;
    rhs = ht_normalize(s, rhs, HT_NF);
    if (rhs == HT_NONE) {
        goto finish;
    }
    for (size_t i = 0; i < arity; ++i) {
        if (!push_term(s, &normalized, ht_normalize(s, parameters[i], HT_NF))) {
            goto finish;
        }
    }
    HTerm body = rhs;
    while (s->nodes[body].tag == HT_LAM) {
        TermNode n = s->nodes[body];
        if (!push_word(s, &lambda_hints, n.meta)) {
            goto finish;
        }
        body = ht_deref(s, n.a);
    }
    if (!ht_spine(s, body, &body_spine)) {
        goto finish;
    }
    if (ht_deref(s, body_spine.head) == variable) {
        if (!lhs_arguments(s, normalized.items, normalized.count, lambda_hints.count, &lhs)) {
            goto finish;
        }
        if (lhs.count != body_spine.count) {
            status = 2;
            goto finish;
        }
        int identical = 1;
        for (size_t i = 0; i < lhs.count; ++i) {
            if (equal(s, lhs.items[i], body_spine.args[i], 0)) {
                if (!push_term(s, &common, ht_index(s, lhs.count - i - 1))) {
                    goto finish;
                }
            } else {
                identical = 0;
            }
        }
        if (identical) {
            status = 1;
            goto finish;
        }
        if (!pattern(s, variable, body_spine.args, body_spine.count)) {
            status = 2;
            goto finish;
        }
        if (!parameter_hints(s, normalized.items, normalized.count, outer, &hints)) {
            goto finish;
        }
        for (size_t i = 0; i < lambda_hints.count; ++i) {
            if (!push_word(s, &hints, lambda_hints.items[i])) {
                goto finish;
            }
        }
        HTerm head = ht_var(s, s->nodes[variable].scope, s->nodes[variable].is_type, -1);
        HTerm replacement = abstractions(s, applications(s, head, common.items, common.count), hints.items, hints.count);
        status = replacement == HT_NONE ? -1 : assign(s, variable, replacement);
    } else {
        if (!pattern(s, variable, normalized.items, normalized.count)) {
            status = 2;
            goto finish;
        }
        HTerm replacement;
        status = bind_value(s, variable, rhs, normalized.items, normalized.count, outer, &bound, &replacement, 0);
        if (status != 1) {
            goto finish;
        }
        if (!parameter_hints(s, normalized.items, normalized.count, outer, &hints)) {
            status = -1;
            goto finish;
        }
        replacement = abstractions(s, replacement, hints.items, hints.count);
        status = replacement == HT_NONE ? -1 : assign(s, variable, replacement);
    }
finish:
    free(normalized.items);
    free(lhs.items);
    free(common.items);
    free(lambda_hints.items);
    free(hints.items);
    free(bound.items);
    ht_spine_free(&body_spine);
    if (status != 1) {
        ht_restore(s, checkpoint);
        s->changes = changes;
    }
    return s->error[0] ? -1 : status;
}

typedef struct { HTerm left, right; } Equation;
typedef struct { Equation *items; size_t count, capacity; } Equations;

static int add_equation(HolTermStore *s, Equations *equations, HTerm left, HTerm right)
{
    if (left == HT_NONE || right == HT_NONE || !reserve(s, (void **) &equations->items, &equations->capacity, equations->count + 1, sizeof(*equations->items))) {
        return 0;
    }
    equations->items[equations->count++] = (Equation) { left, right };
    return 1;
}

static int solve_pair(HolTermStore *s, HTerm left, HTerm right, Words *outer, Equations *delayed, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return -1;
    }
    left = ht_normalize(s, left, HT_NF);
    right = ht_normalize(s, right, HT_NF);
    if (left == HT_NONE || right == HT_NONE) {
        return -1;
    }
    if (equal(s, left, right, 0)) {
        return s->error[0] ? -1 : 1;
    }
    TermNode l = s->nodes[left], r = s->nodes[right];
    if (l.tag == HT_NAT && r.tag == HT_NAT) {
        return 0;
    }
    if (l.tag == HT_LAM && r.tag == HT_LAM) {
        if (!push_word(s, outer, l.meta)) {
            return -1;
        }
        int result = solve_pair(s, l.a, r.a, outer, delayed, depth + 1);
        --outer->count;
        return result;
    }
    HTSpine lhs = { 0 }, rhs = { 0 };
    int status = -1;
    if (!ht_spine(s, left, &lhs) || !ht_spine(s, right, &rhs)) {
        goto finish;
    }
    HTerm lh = ht_deref(s, lhs.head), rh = ht_deref(s, rhs.head);
    if ((l.tag == HT_LAM && rigid(s, rh)) || (r.tag == HT_LAM && rigid(s, lh))) {
        int left_lambda = l.tag == HT_LAM;
        HTerm expansion = shift(s, left_lambda ? right : left, 1, 0, 0);
        HTerm index = ht_index(s, 0);
        expansion = ht_app(s, expansion, index, -1);
        if (expansion == HT_NONE || !push_word(s, outer, left_lambda ? l.meta : r.meta)) {
            goto finish;
        }
        status = solve_pair(s, left_lambda ? l.a : expansion, left_lambda ? expansion : r.a, outer, delayed, depth + 1);
        --outer->count;
    } else if (rigid(s, lh) && rigid(s, rh)) {
        if (!equal(s, lh, rh, 0) || lhs.count != rhs.count) {
            status = 0;
            goto finish;
        }
        status = 1;
        for (size_t i = 0; i < lhs.count && status == 1; ++i) {
            status = solve_pair(s, lhs.args[i], rhs.args[i], outer, delayed, depth + 1);
        }
    } else if (s->nodes[lh].tag == HT_VAR && pattern(s, lh, lhs.args, lhs.count)) {
        status = make_substitution(s, lh, right, lhs.args, lhs.count, outer);
    } else if (s->nodes[rh].tag == HT_VAR && pattern(s, rh, rhs.args, rhs.count)) {
        status = make_substitution(s, rh, left, rhs.args, rhs.count, outer);
    } else if (s->nodes[lh].tag == HT_WILD || s->nodes[rh].tag == HT_WILD) {
        status = 1;
    } else {
        status = 2;
    }
    if (status == 2) {
        HTerm a = abstractions(s, left, outer->items, outer->count);
        HTerm b = abstractions(s, right, outer->items, outer->count);
        status = add_equation(s, delayed, a, b) ? 1 : -1;
    }
finish:
    ht_spine_free(&lhs);
    ht_spine_free(&rhs);
    return s->error[0] ? -1 : status;
}

static int unify_equations(HolTermStore *s, HTerm left, HTerm right, int add_new)
{
    if (!s || s->error[0]) {
        return -1;
    }
    HTCheckpoint checkpoint = ht_checkpoint(s);
    uint64_t initial_changes = s->changes;
    Equations input = { 0 }, output = { 0 };
    Words outer = { 0 };
    int status = -1;
    if (add_new && !add_equation(s, &input, left, right)) {
        goto finish;
    }
    for (size_t item = s->pending_head; item != HT_NONE; item = s->pending[item].next) {
        Pending p = s->pending[item];
        if (!add_equation(s, &input, p.left, p.right)) {
            goto finish;
        }
    }
    for (;;) {
        uint64_t changes = s->changes;
        output.count = 0;
        status = 1;
        for (size_t i = 0; i < input.count && status == 1; ++i) {
            status = solve_pair(s, input.items[i].left, input.items[i].right, &outer, &output, 0);
        }
        if (status != 1) {
            goto finish;
        }
        if (!output.count || s->changes == changes) {
            break;
        }
        Equations swap = input;
        input = output;
        output = swap;
    }
    s->pending_head = HT_NONE;
    for (size_t i = output.count; i > 0; --i) {
        if (!reserve(s, (void **) &s->pending, &s->pending_capacity, s->pending_count + 1, sizeof(*s->pending))) {
            status = -1;
            goto finish;
        }
        Equation eq = output.items[i - 1];
        s->pending[s->pending_count] = (Pending) { eq.left, eq.right, s->pending_head };
        s->pending_head = s->pending_count++;
    }
finish:
    free(input.items);
    free(output.items);
    free(outer.items);
    if (status != 1) {
        ht_restore(s, checkpoint);
        s->changes = initial_changes;
    }
    return s->error[0] ? -1 : status;
}

int ht_unify(HolTermStore *s, HTerm left, HTerm right)
{
    if (!operation_begin(s)) {
        return -1;
    }
    int result = -1;
    if (left >= s->count || right >= s->count) {
        fail(s, "Unification references an invalid term");
    } else {
        result = unify_equations(s, left, right, 1);
    }
    operation_end(s);
    return result;
}

int ht_retry(HolTermStore *s)
{
    if (!operation_begin(s)) {
        return -1;
    }
    int result = unify_equations(s, HT_NONE, HT_NONE, 0);
    operation_end(s);
    return result;
}

static int assignment_scope(HolTermStore *s, HTerm term, size_t scope, size_t binders, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return -1;
    }
    term = ht_deref(s, term);
    if (term == HT_NONE) {
        fail(s, "Invalid checked assignment term");
        return -1;
    }
    TermNode n = s->nodes[term];
    switch (n.tag) {
        case HT_VAR:
        case HT_NOMINAL:
            return n.scope <= scope;
        case HT_INDEX:
            return n.a < binders;
        case HT_LAM:
            return assignment_scope(s, n.a, scope, binders + 1, depth + 1);
        case HT_APP: {
            int left = assignment_scope(s, n.a, scope, binders, depth + 1);
            return left == 1 ? assignment_scope(s, n.b, scope, binders, depth + 1) : left;
        }
        default:
            return 1;
    }
}

int ht_assign_checked(HolTermStore *s, HTerm variable, HTerm value)
{
    if (!operation_begin(s)) {
        return -1;
    }
    HTCheckpoint checkpoint = ht_checkpoint(s);
    uint64_t changes = s->changes;
    int status = -1;
    if (variable >= s->count || value >= s->count || s->nodes[variable].tag != HT_VAR) {
        fail(s, "Checked assignment target is not a variable");
    } else {
        HTerm target = ht_deref(s, variable);
        if (s->nodes[target].tag != HT_VAR) {
            status = ht_unify(s, target, value);
        } else {
            value = ht_normalize(s, value, HT_NF);
            if (value != HT_NONE) {
                status = assignment_scope(s, value, s->nodes[target].scope, 0, 0);
                if (status == 1) {
                    status = assign(s, target, value);
                }
                if (status == 1) {
                    status = ht_retry(s);
                }
            }
        }
    }
    if (status != 1) {
        ht_restore(s, checkpoint);
        s->changes = changes;
    }
    operation_end(s);
    return s->error[0] ? -1 : status;
}

size_t ht_pending_count(const HolTermStore *s)
{
    size_t count = 0;
    for (size_t item = s->pending_head; item != HT_NONE; item = s->pending[item].next) {
        ++count;
    }
    return count;
}

int ht_pending(const HolTermStore *s, size_t index, HTerm *left, HTerm *right)
{
    size_t item = s->pending_head;
    while (item != HT_NONE && index) {
        item = s->pending[item].next;
        --index;
    }
    if (item == HT_NONE) {
        return 0;
    }
    *left = s->pending[item].left;
    *right = s->pending[item].right;
    return 1;
}

static int read_word(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, int64_t *value)
{
    if (*offset >= count) {
        return fail(s, "Truncated term wire");
    }
    *value = words[(*offset)++];
    return 1;
}

static HTerm import_term(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, size_t depth, int restoring)
{
    int64_t tag, a, b, c, d;
    if (!depth_okay(s, depth) || !read_word(s, words, count, offset, &tag)) {
        return HT_NONE;
    }
    switch (tag) {
        case HT_VAR:
        case HT_NOMINAL: {
            if (!read_word(s, words, count, offset, &a) || !read_word(s, words, count, offset, &b) || !read_word(s, words, count, offset, &c)) {
                return HT_NONE;
            }
            if (tag == HT_VAR) {
                if (!read_word(s, words, count, offset, &d)) {
                    return HT_NONE;
                }
            } else {
                d = c;
                c = 0;
            }
            if (a < 0 || b < 0 || (uint64_t) b > SIZE_MAX || d < -1 || (c != 0 && c != 1)) {
                fail(s, "Invalid variable wire metadata");
                return HT_NONE;
            }
            HTerm previous = ht_lookup_uid(s, (uint64_t) a);
            if (previous != HT_NONE) {
                TermNode n = s->nodes[previous];
                if (n.tag != tag || n.is_type != c || (tag == HT_NOMINAL && n.scope != (size_t) b)) {
                    fail(s, "Conflicting term identity metadata");
                    return HT_NONE;
                }
                return previous;
            }
            if (s->identity_capacity) {
                size_t index = bucket((uint64_t) a, s->identity_capacity);
                while (s->identities[index].uid != UID_EMPTY) {
                    if (s->identities[index].uid == (uint64_t) a && !restoring) {
                        fail(s, "Term wire refers to an expired identity");
                        return HT_NONE;
                    }
                    index = (index + 1) & (s->identity_capacity - 1);
                }
            }
            return identity_node(s, (int) tag, (uint64_t) a, (size_t) b, (int) c, d, restoring);
        }
        case HT_CONST:
            if (!read_word(s, words, count, offset, &a) || !read_word(s, words, count, offset, &b) || a < 0 || (uint64_t) a > SIZE_MAX || b < -1) {
                fail(s, "Invalid constant wire");
                return HT_NONE;
            }
            return ht_constant(s, (size_t) a, b);
        case HT_APP: {
            if (!read_word(s, words, count, offset, &a) || a < -1) {
                fail(s, "Invalid application wire");
                return HT_NONE;
            }
            HTerm function = import_term(s, words, count, offset, depth + 1, restoring);
            HTerm argument = import_term(s, words, count, offset, depth + 1, restoring);
            return ht_app(s, function, argument, a);
        }
        case HT_INDEX:
            if (!read_word(s, words, count, offset, &a) || a < 0 || (uint64_t) a > SIZE_MAX) {
                fail(s, "Invalid bound variable wire");
                return HT_NONE;
            }
            return ht_index(s, (size_t) a);
        case HT_LAM: {
            if (!read_word(s, words, count, offset, &a) || a < -1) {
                fail(s, "Invalid lambda wire");
                return HT_NONE;
            }
            HTerm body = import_term(s, words, count, offset, depth + 1, restoring);
            return ht_lam(s, body, a);
        }
        case HT_NAT: {
            if (!read_word(s, words, count, offset, &a) || a <= 0 || (uint64_t) a > count - *offset) {
                fail(s, "Invalid natural wire size");
                return HT_NONE;
            }
            size_t length = (size_t) a;
            char *digits = malloc(length + 1);
            if (!digits) {
                fail(s, "Natural wire allocation failed");
                return HT_NONE;
            }
            for (size_t i = 0; i < length; ++i) {
                int64_t digit = words[(*offset)++];
                if (digit < '0' || digit > '9') {
                    free(digits);
                    fail(s, "Invalid natural wire digit");
                    return HT_NONE;
                }
                digits[i] = (char) digit;
            }
            digits[length] = '\0';
            HTerm result = ht_nat(s, digits);
            free(digits);
            return result;
        }
        case HT_WILD:
            return ht_wildcard(s);
        default:
            fail(s, "Invalid term wire tag");
            return HT_NONE;
    }
}

static HTerm import_wire(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, int restoring)
{
    if (!s || s->error[0] || !offset || *offset > count || (count && !words)) {
        fail(s, "Invalid term wire input");
        return HT_NONE;
    }
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTCheckpoint checkpoint = ht_checkpoint(s);
    size_t previous = *offset;
    HTerm term = import_term(s, words, count, offset, 0, restoring);
    if (term == HT_NONE) {
        ht_restore(s, checkpoint);
        *offset = previous;
    }
    operation_end(s);
    return term;
}

HTerm ht_import(HolTermStore *s, const int64_t *words, size_t count, size_t *offset)
{
    return import_wire(s, words, count, offset, 0);
}

HTerm ht_import_restored(HolTermStore *s, const int64_t *words, size_t count, size_t *offset)
{
    return import_wire(s, words, count, offset, 1);
}

static int export_term(HolTermStore *s, HTerm term, Words *words, size_t depth)
{
    if (!depth_okay(s, depth)) {
        return 0;
    }
    term = ht_deref(s, term);
    if (term == HT_NONE) {
        return fail(s, "Invalid term export reference");
    }
    TermNode n = s->nodes[term];
    if (!push_word(s, words, n.tag)) {
        return 0;
    }
    switch (n.tag) {
        case HT_VAR:
            return push_word(s, words, (int64_t) n.uid) && push_word(s, words, (int64_t) n.scope) && push_word(s, words, n.is_type) && push_word(s, words, n.meta);
        case HT_CONST:
            return push_word(s, words, (int64_t) n.a) && push_word(s, words, n.meta);
        case HT_APP:
            return push_word(s, words, n.meta) && export_term(s, n.a, words, depth + 1) && export_term(s, n.b, words, depth + 1);
        case HT_INDEX:
            return push_word(s, words, (int64_t) n.a);
        case HT_LAM:
            return push_word(s, words, n.meta) && export_term(s, n.a, words, depth + 1);
        case HT_NOMINAL:
            return push_word(s, words, (int64_t) n.uid) && push_word(s, words, (int64_t) n.scope) && push_word(s, words, n.meta);
        case HT_NAT: {
            size_t length = strlen(n.digits);
            if (length > INT64_MAX || !push_word(s, words, (int64_t) length)) {
                return fail(s, "Natural export length overflow");
            }
            for (size_t i = 0; i < length; ++i) {
                if (!push_word(s, words, n.digits[i])) {
                    return 0;
                }
            }
            return 1;
        }
        case HT_WILD:
            return 1;
        default:
            return fail(s, "Invalid term export tag");
    }
}

int ht_export(HolTermStore *s, HTerm term, int64_t **words, size_t *count)
{
    if (!words || !count) {
        return fail(s, "Invalid term export buffer");
    }
    *words = NULL;
    *count = 0;
    if (!operation_begin(s)) {
        return 0;
    }
    Words output = { 0 };
    term = ht_normalize(s, term, HT_NF);
    if (term == HT_NONE || !export_term(s, term, &output, 0)) {
        free(output.items);
        operation_end(s);
        return 0;
    }
    *words = output.items;
    *count = output.count;
    operation_end(s);
    return 1;
}

HolTermStore *ht_clone(const HolTermStore *source)
{
    if (!source) {
        return NULL;
    }
    HolTermStore *copy = ht_create();
    if (!copy) {
        return NULL;
    }
    copy->next_uid = source->next_uid;
    copy->successor = source->successor;
    copy->work_limit = source->work_limit;
    if (source->opaque_count) {
        if (!reserve(copy, (void **) &copy->opaque, &copy->opaque_capacity, source->opaque_count, sizeof(*copy->opaque))) {
            ht_destroy(copy);
            return NULL;
        }
        memcpy(copy->opaque, source->opaque, source->opaque_count);
        copy->opaque_count = source->opaque_count;
    }
    copy->changes = source->changes;
    if (!reserve(copy, (void **) &copy->nodes, &copy->capacity, source->count, sizeof(*copy->nodes)) || !reserve(copy, (void **) &copy->trail, &copy->trail_capacity, source->trail_count, sizeof(*copy->trail)) || !reserve(copy, (void **) &copy->pending, &copy->pending_capacity, source->pending_count, sizeof(*copy->pending))) {
        ht_destroy(copy);
        return NULL;
    }
    for (size_t i = 0; i < source->count; ++i) {
        TermNode n = source->nodes[i];
        if (n.digits) {
            size_t length = strlen(n.digits);
            n.digits = malloc(length + 1);
            if (!n.digits) {
                ht_destroy(copy);
                return NULL;
            }
            memcpy(n.digits, source->nodes[i].digits, length + 1);
        }
        copy->nodes[copy->count++] = n;
    }
    if (source->identity_capacity) {
        copy->identities = malloc(source->identity_capacity * sizeof(*copy->identities));
        if (!copy->identities) {
            ht_destroy(copy);
            return NULL;
        }
        memcpy(copy->identities, source->identities, source->identity_capacity * sizeof(*copy->identities));
        copy->identity_capacity = source->identity_capacity;
        copy->identity_count = source->identity_count;
        }
    if (source->trail_count) {
        memcpy(copy->trail, source->trail, source->trail_count * sizeof(*copy->trail));
    }
    if (source->pending_count) {
        memcpy(copy->pending, source->pending, source->pending_count * sizeof(*copy->pending));
    }
    copy->trail_count = source->trail_count;
    copy->pending_count = source->pending_count;
    copy->pending_head = source->pending_head;
    memcpy(copy->error, source->error, sizeof(copy->error));
    return copy;
}

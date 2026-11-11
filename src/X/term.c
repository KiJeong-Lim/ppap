#include "term.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define UID_EMPTY UINT64_MAX
#define WORK_LIMIT UINT64_C(5000000)

/* A stable node has no variable, wildcard or opaque constant below it, so no
    * binding can change it. Its summary is exact: whether it is beta-normal,
    * whether it is eta-normal, whether an arithmetic constant occurs in it, the
    * largest scope of its nominals (scope), one more than its largest loose index
    * (open), and its loose indices below 32 that certainly occur (mask). */
enum { HS_STABLE = 1, HS_BETA = 2, HS_ETA = 4, HS_ARITHMETIC = 8 };
/* A form of normalize alone: the full normal form of a term that is known to
    * be weak-head normal and no abstraction. */
enum { FORM_SPINE = HT_NF + 1 };
enum { MARK_OPAQUE = 1, MARK_ARITHMETIC = 2 };
#define HS_NORMAL (HS_STABLE | HS_BETA | HS_ETA)
#define OPEN_UNKNOWN UINT32_MAX

typedef struct {
    int tag;
    unsigned char is_type, ground, pinned, summary;
    HTerm a, b;
    uint64_t uid;
    size_t scope;
    int64_t meta;
    char *digits;
    uint32_t open, mask;
} TermNode;

/* One pending step of a traversal (see enter). */
typedef struct {
    HTerm term, left;
    size_t level;
    unsigned char stage, form;
} Frame;

typedef struct { HTerm variable, binding; size_t scope; } Trail;
typedef struct { HTerm left, right; size_t next; } Pending;
typedef struct { uint64_t uid; HTerm term; } Identity;
typedef struct { uint64_t first, end; } RetiredRange;
typedef struct { HTerm left, right; } Equation;
typedef struct { Equation *items; size_t count, capacity; } Equations;
typedef struct { int64_t *items; size_t count, capacity; } Words;
/* An argument pair that waits while the pairs before it are solved. */
typedef struct { HTerm left, right; size_t binders; uint64_t known; } Pair;

struct HolTermStore {
    TermNode *nodes;
    size_t count, capacity;
    Trail *trail;
    size_t trail_count, trail_capacity;
    Pending *pending;
    size_t pending_count, pending_capacity, pending_head;
    Identity *identities;
    size_t identity_capacity, identity_count, identity_peak;
    RetiredRange *retired;
    size_t retired_count, retired_capacity;
    uint64_t next_uid;
    size_t successor, sealed;
    unsigned char *marks;
    size_t mark_count, mark_capacity;
    uint64_t work, work_limit;
    size_t operations;
    Frame *frames;
    size_t frame_count, frame_capacity;
    Pair *pairs;
    size_t pair_count, pair_capacity;
    /* The buffers of the unifier, kept between two unifications. */
    Equations solving, delayed;
    Words binders;
    int unifying;
    uint64_t changes;
    char error[192];
};

typedef struct { HTerm *items; size_t count, capacity; } Terms;

static int marked(const HolTermStore *s, size_t symbol, unsigned char mark)
{
    return symbol < s->mark_count && (s->marks[symbol] & mark);
}

/* Only immutable, already-normal rigid constructor trees qualify. In
    * particular, a variable currently bound to such a tree does not qualify. */
static int ground_node(const HolTermStore *s, TermNode n)
{
    if (n.tag == HT_NAT) return 1;
    if (n.tag == HT_CONST) return !marked(s, n.a, MARK_OPAQUE);
    if (n.tag != HT_APP || !s->nodes[n.a].ground || !s->nodes[n.b].ground) return 0;
    TermNode function = s->nodes[n.a], argument = s->nodes[n.b];
    return function.tag != HT_CONST || function.a != s->successor || argument.tag != HT_NAT;
}

/* The children of a node precede it, so their summaries are already known. A
    * variable or a nominal keeps its own scope. */
static void summarize(const HolTermStore *s, TermNode *n)
{
    n->ground = ground_node(s, *n);
    n->summary = 0;
    n->open = 0;
    n->mask = 0;
    if (n->tag == HT_VAR) return;
    if (n->tag == HT_NOMINAL) {
        n->summary = HS_NORMAL;
        return;
    }
    n->scope = 0;
    if (n->tag == HT_CONST) {
        if (marked(s, n->a, MARK_OPAQUE)) return;
        n->summary = HS_NORMAL | (n->a == s->successor || marked(s, n->a, MARK_ARITHMETIC) ? HS_ARITHMETIC : 0);
    } else if (n->tag == HT_NAT) {
        n->summary = HS_NORMAL;
    } else if (n->tag == HT_INDEX) {
        n->summary = HS_NORMAL;
        n->open = n->a < OPEN_UNKNOWN - 1 ? (uint32_t) n->a + 1 : OPEN_UNKNOWN;
        n->mask = n->a < 32 ? UINT32_C(1) << n->a : 0;
    } else if (n->tag == HT_APP) {
        TermNode f = s->nodes[n->a], x = s->nodes[n->b];
        if (!(f.summary & x.summary & HS_STABLE)) return;
        int redex = f.tag == HT_LAM || (f.tag == HT_CONST && f.a == s->successor && x.tag == HT_NAT);
        n->summary = (unsigned char) (HS_STABLE | (f.summary & x.summary & (HS_BETA | HS_ETA)) | ((f.summary | x.summary) & HS_ARITHMETIC));
        if (redex) n->summary &= (unsigned char) ~HS_BETA;
        n->scope = f.scope > x.scope ? f.scope : x.scope;
        n->open = f.open > x.open ? f.open : x.open;
        n->mask = f.mask | x.mask;
    } else if (n->tag == HT_LAM) {
        TermNode body = s->nodes[n->a];
        if (!(body.summary & HS_STABLE)) return;
        /* body = f #0 is an eta-redex unless #0 certainly occurs in f */
        int redex = body.tag == HT_APP && s->nodes[body.b].tag == HT_INDEX && !s->nodes[body.b].a && !(s->nodes[body.a].mask & 1);
        n->summary = body.summary;
        if (redex) n->summary &= (unsigned char) ~HS_ETA;
        n->scope = body.scope;
        n->open = body.open == OPEN_UNKNOWN ? OPEN_UNKNOWN : body.open ? body.open - 1 : 0;
        n->mask = body.mask >> 1;
    }
}

static void refresh_summaries(HolTermStore *s)
{
    for (size_t i = 0; i < s->count; ++i) summarize(s, &s->nodes[i]);
}

static int stable(TermNode n)
{
    return n.summary & HS_STABLE;
}

static int normal(TermNode n)
{
    return (n.summary & HS_NORMAL) == HS_NORMAL;
}

/* A stable node all of whose loose indices are below limit. */
static int closed_below(TermNode n, size_t limit)
{
    return (n.summary & HS_STABLE) && n.open != OPEN_UNKNOWN && n.open <= limit;
}

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

static int grow(HolTermStore *s, void **pointer, size_t *capacity, size_t count, size_t width);

static inline int reserve(HolTermStore *s, void **pointer, size_t *capacity, size_t count, size_t width)
{
    return count <= *capacity || grow(s, pointer, capacity, count, width);
}

static int grow(HolTermStore *s, void **pointer, size_t *capacity, size_t count, size_t width)
{
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
    summarize(s, &value);
    s->nodes[result] = value;
    return result;
}

static size_t bucket(uint64_t uid, size_t capacity)
{
    return (size_t) (uid * UINT64_C(11400714819323198485)) & (capacity - 1);
}

static int identity_retired(const HolTermStore *s, uint64_t uid)
{
    size_t first = 0, end = s->retired_count;
    if (!end || uid >= s->retired[end - 1].end) {
        return 0;
    }
    while (first < end) {
        size_t middle = first + (end - first) / 2;
        RetiredRange range = s->retired[middle];
        if (uid < range.first) {
            end = middle;
        } else if (uid >= range.end) {
            first = middle + 1;
        } else {
            return 1;
        }
    }
    return 0;
}

/* Every live identity can add at most one range when rolled back. Reserving
    * that space before allocation keeps retirement allocation-free. */
static int reserve_retired(HolTermStore *s, size_t extra)
{
    if (s->identity_count > SIZE_MAX - s->retired_count || extra > SIZE_MAX - s->retired_count - s->identity_count) {
        return fail(s, "Retired identity table overflow");
    }
    return reserve(s, (void **) &s->retired, &s->retired_capacity, s->retired_count + s->identity_count + extra, sizeof(*s->retired));
}

static int retire_range(HolTermStore *s, uint64_t first, uint64_t end)
{
    size_t low = 0, high = s->retired_count;
    while (low < high) {
        size_t middle = low + (high - low) / 2;
        if (s->retired[middle].end < first) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    size_t after = low;
    while (after < s->retired_count && s->retired[after].first <= end) {
        RetiredRange range = s->retired[after++];
        if (range.first < first) first = range.first;
        if (range.end > end) end = range.end;
    }
    if (after == low) {
        if (s->retired_count == s->retired_capacity) {
            return fail(s, "Missing retired identity capacity");
        }
        memmove(s->retired + low + 1, s->retired + low, (s->retired_count - low) * sizeof(*s->retired));
        ++s->retired_count;
    } else {
        memmove(s->retired + low + 1, s->retired + after, (s->retired_count - after) * sizeof(*s->retired));
        s->retired_count -= after - low - 1;
    }
    s->retired[low] = (RetiredRange) { first, end };
    return 1;
}

static int rehash_identities(HolTermStore *s, size_t capacity)
{
    Identity *table = malloc(capacity * sizeof(*table));
    if (!table) {
        return 0;
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

static int reserve_identities(HolTermStore *s)
{
    if (s->identity_capacity && s->identity_count < s->identity_capacity / 2) {
        return 1;
    }
    size_t capacity = s->identity_capacity ? s->identity_capacity * 2 : 64;
    if (capacity < s->identity_capacity || capacity > SIZE_MAX / sizeof(Identity)) {
        return fail(s, "Term identity table overflow");
    }
    return rehash_identities(s, capacity) || fail(s, "Term identity allocation failed");
}

static int insert_identity(HolTermStore *s, uint64_t uid, HTerm term, int restoring)
{
    if (!restoring && identity_retired(s, uid)) {
        return fail(s, "Term wire refers to an expired identity");
    }
    if (!reserve_identities(s) || !reserve_retired(s, 1)) {
        return 0;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            return fail(s, "Duplicate term identity");
        }
        index = (index + 1) & (s->identity_capacity - 1);
    }
    s->identities[index] = (Identity) { uid, term };
    if (++s->identity_count > s->identity_peak) {
        s->identity_peak = s->identity_count;
    }
    return 1;
}

/* The uids are sorted. Every one of them is live, so the ranges have room for
    * them (reserve_retired); a pass from the largest down merges them in place.
    * Retiring them one by one would move the ranges above each of them. */
static void retire_sorted(HolTermStore *s, const uint64_t *uids, size_t count)
{
    RetiredRange *ranges = s->retired;
    size_t total = s->retired_count + count, write = total, i = s->retired_count, j = count;
    if (!count) {
        return;
    }
    while (i || j) {
        RetiredRange next;
        if (j && (!i || uids[j - 1] >= ranges[i - 1].first)) {
            --j;
            next = (RetiredRange) { uids[j], uids[j] + 1 };
        } else {
            next = ranges[--i];
        }
        if (write < total && next.end >= ranges[write].first) {
            ranges[write].first = next.first;
            if (next.end > ranges[write].end) {
                ranges[write].end = next.end;
            }
        } else {
            ranges[--write] = next;
        }
    }
    memmove(ranges, ranges + write, (total - write) * sizeof(*ranges));
    s->retired_count = total - write;
}

static int ascending(const void *left, const void *right)
{
    uint64_t a = *(const uint64_t *) left, b = *(const uint64_t *) right;
    return a < b ? -1 : a > b;
}

/* retire is 0 when the caller retires the uid itself (retire_sorted). */
static void remove_identity(HolTermStore *s, uint64_t uid, int retire)
{
    if (!s->identity_capacity) {
        return;
    }
    size_t index = bucket(uid, s->identity_capacity);
    while (s->identities[index].uid != UID_EMPTY) {
        if (s->identities[index].uid == uid) {
            if (retire && !retire_range(s, uid, uid + 1)) {
                return;
            }
            --s->identity_count;
            size_t mask = s->identity_capacity - 1;
            size_t next = (index + 1) & mask;
            while (s->identities[next].uid != UID_EMPTY) {
                size_t home = bucket(s->identities[next].uid, s->identity_capacity);
                if (((next - home) & mask) >= ((index - home) & mask)) {
                    s->identities[index] = s->identities[next];
                    index = next;
                }
                next = (next + 1) & mask;
            }
            s->identities[index] = (Identity) { UID_EMPTY, HT_NONE };
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
        s->work_limit = WORK_LIMIT;
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
    free(s->retired);
    free(s->marks);
    free(s->frames);
    free(s->pairs);
    free(s->solving.items);
    free(s->delayed.items);
    free(s->binders.items);
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
            remove_identity(s, old.uid, 1);
        }
        free(old.digits);
    }
    if (s->sealed > s->count) {
        s->sealed = s->count;
    }
    s->pending_count = saved.pending;
    s->pending_head = saved.pending_head;
    return 1;
}

static void release_spare(void **pointer, size_t *capacity, size_t count, size_t limit)
{
    if (!count && *capacity > limit) {
        free(*pointer);
        *pointer = NULL;
        *capacity = 0;
    }
}

int ht_reset(HolTermStore *s, size_t heap, uint64_t next_uid, size_t symbols)
{
    if (!s || s->error[0] || s->operations || next_uid > s->next_uid) {
        return fail(s, "Invalid term store reset");
    }
    if (!ht_restore(s, (HTCheckpoint) { heap, 0, 0, HT_NONE })) {
        return 0;
    }
    while (s->retired_count && s->retired[s->retired_count - 1].first >= next_uid) {
        --s->retired_count;
    }
    if (s->retired_count && s->retired[s->retired_count - 1].end > next_uid) {
        s->retired[s->retired_count - 1].end = next_uid;
    }
    s->next_uid = next_uid;
    if (s->mark_count > symbols) {
        s->mark_count = symbols;
    }
    s->work_limit = WORK_LIMIT;
    s->work = 0;
    s->frame_count = 0;
    if (s->capacity / 4 > s->count && s->capacity > 1024) {
        size_t capacity = s->count * 2 > 1024 ? s->count * 2 : 1024;
        TermNode *smaller = realloc(s->nodes, capacity * sizeof(*smaller));
        if (smaller) {
            s->nodes = smaller;
            s->capacity = capacity;
        }
    }
    s->identity_peak = s->identity_count;
    if (s->identity_capacity / 8 > s->identity_count && s->identity_capacity > 64) {
        size_t capacity = 64;
        while (capacity / 4 < s->identity_count) {
            capacity *= 2;
        }
        rehash_identities(s, capacity);
    }
    release_spare((void **) &s->trail, &s->trail_capacity, s->trail_count, 4096);
    release_spare((void **) &s->pending, &s->pending_capacity, s->pending_count, 4096);
    release_spare((void **) &s->retired, &s->retired_capacity, s->retired_count, 4096);
    release_spare((void **) &s->frames, &s->frame_capacity, s->frame_count, 4096);
    s->pair_count = 0;
    release_spare((void **) &s->pairs, &s->pair_capacity, 0, 4096);
    release_spare((void **) &s->solving.items, &s->solving.capacity, 0, 4096);
    release_spare((void **) &s->delayed.items, &s->delayed.capacity, 0, 4096);
    release_spare((void **) &s->binders.items, &s->binders.capacity, 0, 4096);
    return 1;
}

size_t ht_seal(HolTermStore *s)
{
    while (s->sealed < s->count && s->nodes[s->sealed].tag != HT_VAR) {
        ++s->sealed;
    }
    return s->sealed;
}

size_t ht_sealed(const HolTermStore *s)
{
    return s->sealed;
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
    for (size_t i = 0; i < live->retired_count; ++i) {
        RetiredRange range = live->retired[i];
        if (!reserve_retired(restored, 1) || !retire_range(restored, range.first, range.end)) {
            return 0;
        }
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
        if (!present && (!reserve_retired(restored, 1) || !retire_range(restored, entry.uid, entry.uid + 1))) {
            return 0;
        }
    }
    return ht_advance_uid(restored, live->next_uid);
}

void ht_set_successor(HolTermStore *s, size_t symbol)
{
    s->successor = symbol;
    refresh_summaries(s);
}

static int mark_symbol(HolTermStore *s, size_t symbol, unsigned char mark, const char *invalid)
{
    if (!s || s->error[0] || symbol >= INT64_MAX || symbol == SIZE_MAX) {
        return fail(s, invalid);
    }
    size_t count = symbol + 1;
    if (!reserve(s, (void **) &s->marks, &s->mark_capacity, count, sizeof(*s->marks))) {
        return 0;
    }
    if (count > s->mark_count) {
        memset(s->marks + s->mark_count, 0, count - s->mark_count);
        s->mark_count = count;
    }
    if (!(s->marks[symbol] & mark)) {
        s->marks[symbol] |= mark;
        refresh_summaries(s);
    }
    return 1;
}

int ht_set_opaque_symbol(HolTermStore *s, size_t symbol)
{
    return mark_symbol(s, symbol, MARK_OPAQUE, "Invalid opaque symbol");
}

int ht_set_arithmetic_symbol(HolTermStore *s, size_t symbol)
{
    return mark_symbol(s, symbol, MARK_ARITHMETIC, "Invalid arithmetic symbol");
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
    HTerm result = node(s, (TermNode) { tag, is_type, 0, 0, 0, HT_NONE, HT_NONE, uid, scope, meta, NULL, 0, 0 });
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
    return node(s, (TermNode) { HT_CONST, 0, 0, 0, 0, symbol, HT_NONE, 0, 0, meta, NULL, 0, 0 });
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
    HTerm result = node(s, (TermNode) { HT_NAT, 0, 0, 0, 0, HT_NONE, HT_NONE, 0, 0, -1, copy, 0, 0 });
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
    return node(s, (TermNode) { HT_INDEX, 0, 0, 0, 0, index, HT_NONE, 0, 0, -1, NULL, 0, 0 });
}

HTerm ht_lam(HolTermStore *s, HTerm body, int64_t meta)
{
    if (body >= s->count || meta < -1) {
        fail(s, "Invalid lambda term");
        return HT_NONE;
    }
    return node(s, (TermNode) { HT_LAM, 0, 0, 0, 0, body, HT_NONE, 0, 0, meta, NULL, 0, 0 });
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
    return node(s, (TermNode) { HT_APP, 0, 0, 0, 0, function, argument, 0, 0, meta, NULL, 0, 0 });
}

HTerm ht_wildcard(HolTermStore *s)
{
    return node(s, (TermNode) { HT_WILD, 0, 0, 0, 0, HT_NONE, HT_NONE, 0, 0, -1, NULL, 0, 0 });
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

/* A parent whose rebuilt children are the dereferences of its own children is
    * returned as it is: every reader dereferences a child before inspecting it. */
static int unchanged(const HolTermStore *s, HTerm result, HTerm original)
{
    return result == original || (result != HT_NONE && result == ht_deref(s, original));
}

static int work_okay(HolTermStore *s)
{
    if (s->work >= s->work_limit) {
        return fail(s, "Native term work limit exceeded");
    }
    ++s->work;
    return 1;
}

/* The traversals below keep their pending steps in s->frames instead of the C
    * stack, so that the depth of a term is bounded by memory alone. An operation
    * owns the frames above the count it found, and a nested operation stacks its
    * own on top. A frame is read by value: entering a term can move the array. */
static int enter(HolTermStore *s, HTerm term, size_t level, int form)
{
    if (term == HT_NONE || !reserve(s, (void **) &s->frames, &s->frame_capacity, s->frame_count + 1, sizeof(*s->frames))) {
        return 0;
    }
    s->frames[s->frame_count++] = (Frame) { term, HT_NONE, level, 0, (unsigned char) form };
    return 1;
}

/* The four rewritings of loose indices. level is the number of binders above
    * the node: an index below it is bound inside the term and stays. */
enum { MAP_SHIFT, MAP_SUBSTITUTE, MAP_INSTANTIATE, MAP_REMOVE };

typedef struct {
    int kind;
    size_t amount;
    HTerm argument;
    const HTerm *values;
    size_t count;
} IndexMap;

static HTerm map_indices(HolTermStore *s, HTerm root, size_t level, const IndexMap *map);

static HTerm shift(HolTermStore *s, HTerm term, size_t amount, size_t cutoff)
{
    IndexMap map = { MAP_SHIFT, amount, HT_NONE, NULL, 0 };
    if (!amount) {
        return term != HT_NONE && work_okay(s) ? ht_deref(s, term) : HT_NONE;
    }
    return map_indices(s, term, cutoff, &map);
}

static HTerm map_index(HolTermStore *s, HTerm term, size_t index, size_t level, const IndexMap *map)
{
    switch (map->kind) {
        case MAP_SHIFT:
            if (index < level) {
                return term;
            }
            if (index > INT64_MAX - map->amount) {
                fail(s, "Bound variable shift overflow");
                return HT_NONE;
            }
            return ht_index(s, index + map->amount);
        case MAP_SUBSTITUTE:
            if (index == level) {
                return shift(s, map->argument, level, 0);
            }
            return index > level ? ht_index(s, index - 1) : term;
        case MAP_INSTANTIATE:
            if (index < level) {
                return term;
            }
            return index - level < map->count ? map->values[map->count - 1 - (index - level)] : ht_index(s, index - map->count);
        default:
            return index > level ? ht_index(s, index - 1) : term;
    }
}

/* Stages of a frame: 0 not visited yet; 1 an application whose function is
    * being rewritten; 2 its argument; 3 an abstraction whose body is. */
static HTerm map_indices(HolTermStore *s, HTerm root, size_t level, const IndexMap *map)
{
    size_t base = s->frame_count;
    HTerm result = HT_NONE;
    if (root != HT_NONE && closed_below(s->nodes[ht_deref(s, root)], level + (map->kind == MAP_REMOVE))) {
        return work_okay(s) ? ht_deref(s, root) : HT_NONE;
    }
    if (!enter(s, root, level, 0)) {
        return HT_NONE;
    }
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (frame.stage == 0) {
            if (!work_okay(s)) {
                break;
            }
            HTerm term = ht_deref(s, frame.term);
            TermNode n = s->nodes[term];
            if (closed_below(n, frame.level + (map->kind == MAP_REMOVE))) {
                result = term;
            } else if (n.tag == HT_INDEX) {
                result = map_index(s, term, n.a, frame.level, map);
            } else if (n.tag == HT_APP || n.tag == HT_LAM) {
                s->frames[s->frame_count - 1].term = term;
                s->frames[s->frame_count - 1].stage = n.tag == HT_APP ? 1 : 3;
                if (!enter(s, n.a, frame.level + (n.tag == HT_LAM), 0)) {
                    break;
                }
                continue;
            } else {
                result = term;
            }
        } else if (frame.stage == 1) {
            s->frames[s->frame_count - 1].left = result;
            s->frames[s->frame_count - 1].stage = 2;
            if (!enter(s, s->nodes[frame.term].b, frame.level, 0)) {
                break;
            }
            continue;
        } else {
            TermNode n = s->nodes[frame.term];
            if (frame.stage == 2) {
                result = unchanged(s, frame.left, n.a) && unchanged(s, result, n.b) ? frame.term : ht_app(s, frame.left, result, n.meta);
            } else {
                result = unchanged(s, result, n.a) ? frame.term : ht_lam(s, result, n.meta);
            }
        }
        if (result == HT_NONE) {
            break;
        }
        --s->frame_count;
    }
    if (s->frame_count > base) {
        s->frame_count = base;
        return HT_NONE;
    }
    return result;
}

static HTerm substitute(HolTermStore *s, HTerm term, HTerm argument, size_t binder)
{
    IndexMap map = { MAP_SUBSTITUTE, 0, argument, NULL, 0 };
    return argument == HT_NONE ? HT_NONE : map_indices(s, term, binder, &map);
}

/* Index i of the body of count nested binders denotes values[count - 1 - i]. */
static HTerm instantiate(HolTermStore *s, HTerm term, const HTerm *values, size_t count, size_t binders)
{
    IndexMap map = { MAP_INSTANTIATE, 0, HT_NONE, values, count };
    return map_indices(s, term, binders, &map);
}

static HTerm remove_binder(HolTermStore *s, HTerm term, size_t index)
{
    IndexMap map = { MAP_REMOVE, 0, HT_NONE, NULL, 0 };
    return map_indices(s, term, index, &map);
}

HTerm ht_instantiate(HolTermStore *s, HTerm body, const HTerm *values, size_t count)
{
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTerm result = HT_NONE;
    int closed = body < s->count && (values || !count);
    for (size_t i = 0; closed && i < count; ++i) {
        closed = values[i] < s->count && (s->nodes[values[i]].tag == HT_VAR || s->nodes[values[i]].tag == HT_NOMINAL);
    }
    if (closed) {
        result = instantiate(s, body, values, count, 0);
    } else {
        fail(s, "Invalid simultaneous instantiation");
    }
    operation_end(s);
    return result;
}

/* Stages of a frame: 0 not visited yet; 1 an application whose function is
    * being brought to weak head normal form; 2 the same function in the form
    * asked for; 3 its argument; 4 an abstraction whose body is being normalized.
    * A beta step visits the same frame again with the contracted term. */
static HTerm normalize(HolTermStore *s, HTerm root, enum HTNormalForm form)
{
    size_t base = s->frame_count;
    HTerm result = HT_NONE;
    if (s->error[0] || root == HT_NONE) {
        return HT_NONE;
    }
    if ((s->nodes[ht_deref(s, root)].summary & (HS_STABLE | HS_BETA)) == (HS_STABLE | HS_BETA)) {
        return work_okay(s) ? ht_deref(s, root) : HT_NONE;
    }
    if (!enter(s, root, 0, form)) {
        return HT_NONE;
    }
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (frame.stage == 0) {
            if (!work_okay(s)) {
                break;
            }
            HTerm term = ht_deref(s, frame.term);
            if (term == HT_NONE) {
                fail(s, "Invalid term reference");
                break;
            }
            TermNode n = s->nodes[term];
            int settled = (n.summary & (HS_STABLE | HS_BETA)) == (HS_STABLE | HS_BETA);
            if (!settled && n.tag == HT_APP) {
                /* An application on a weak-head normal spine has no redex at
                    * its head: its function part is on the same spine. */
                int spine = frame.form == FORM_SPINE;
                s->frames[s->frame_count - 1] = (Frame) { term, HT_NONE, 0, spine ? 2 : 1, (unsigned char) (spine ? HT_NF : frame.form) };
                if (!enter(s, n.a, 0, spine ? FORM_SPINE : HT_WHNF)) {
                    break;
                }
                continue;
            }
            if (!settled && n.tag == HT_LAM && frame.form != HT_WHNF) {
                int form = frame.form == FORM_SPINE ? HT_NF : frame.form;
                s->frames[s->frame_count - 1] = (Frame) { term, HT_NONE, 0, 4, (unsigned char) form };
                if (!enter(s, n.a, 0, form)) {
                    break;
                }
                continue;
            }
            result = term;
        } else if (frame.stage == 4) {
            TermNode n = s->nodes[frame.term];
            result = unchanged(s, result, n.a) ? frame.term : ht_lam(s, result, n.meta);
        } else {
            TermNode n = s->nodes[frame.term];
            HTerm function = frame.stage == 3 ? frame.left : result;
            HTerm argument = frame.stage == 3 ? result : n.b;
            if (frame.stage == 1 && s->nodes[function].tag == HT_LAM) {
                HTerm body = substitute(s, s->nodes[function].a, n.b, 0);
                if (body == HT_NONE) {
                    break;
                }
                s->frames[s->frame_count - 1].term = body;
                s->frames[s->frame_count - 1].stage = 0;
                continue;
            }
            /* The function part is weak-head normal and no abstraction, so
                * it is head normal as well. Its full normal form has the
                * arguments along its spine normalized, and nothing else. */
            if (frame.stage == 1 && frame.form == HT_NF) {
                s->frames[s->frame_count - 1].stage = 2;
                if (!enter(s, function, 0, FORM_SPINE)) {
                    break;
                }
                continue;
            }
            if (frame.stage != 3 && frame.form == HT_NF) {
                s->frames[s->frame_count - 1].left = function;
                s->frames[s->frame_count - 1].stage = 3;
                if (!enter(s, n.b, 0, HT_NF)) {
                    break;
                }
                continue;
            }
            int same = unchanged(s, function, n.a) && unchanged(s, argument, n.b);
            if (same) {
                HTerm arg = ht_deref(s, argument);
                same = arg == HT_NONE || s->nodes[function].tag != HT_CONST || s->nodes[function].a != s->successor || s->nodes[arg].tag != HT_NAT;
            }
            result = same ? frame.term : ht_app(s, function, argument, n.meta);
        }
        if (result == HT_NONE) {
            break;
        }
        --s->frame_count;
    }
    if (s->frame_count > base) {
        s->frame_count = base;
        return HT_NONE;
    }
    return result;
}

HTerm ht_normalize(HolTermStore *s, HTerm term, enum HTNormalForm form)
{
    if (!operation_begin(s)) {
        return HT_NONE;
    }
    HTerm result = normalize(s, term, form);
    operation_end(s);
    return result;
}

HTerm ht_apply(HolTermStore *s, HTerm function, HTerm argument)
{
    return ht_normalize(s, ht_app(s, function, argument, -1), HT_HNF);
}

static int mentions_arithmetic(HolTermStore *s, HTerm term)
{
    size_t base = s->frame_count;
    int found = 0;
    for (;;) {
        if (!work_okay(s)) {
            found = 1;
            break;
        }
        term = ht_deref(s, term);
        TermNode n = s->nodes[term];
        if (!stable(n) && n.tag == HT_APP) {
            if (!enter(s, n.b, 0, 0)) {
                found = 1;
                break;
            }
            term = n.a;
            continue;
        }
        if (!stable(n) && n.tag == HT_LAM) {
            term = n.a;
            continue;
        }
        found = stable(n) ? (n.summary & HS_ARITHMETIC) != 0 : n.tag == HT_CONST;
        if (found || s->frame_count == base) {
            break;
        }
        term = s->frames[--s->frame_count].term;
    }
    s->frame_count = base;
    return found;
}

int ht_mentions_arithmetic(HolTermStore *s, HTerm term)
{
    if (!operation_begin(s)) {
        return -1;
    }
    int result = -1;
    if (term >= s->count) {
        fail(s, "Invalid term reference");
    } else {
        result = mentions_arithmetic(s, term);
    }
    operation_end(s);
    return s->error[0] ? -1 : result;
}

static int spine_view(HolTermStore *s, HTerm term, HTSpine *spine)
{
    *spine = (HTSpine) { HT_NONE, NULL, 0, { 0 } };
    HTerm top = ht_deref(s, term), head = top;
    size_t count = 0;
    while (head != HT_NONE && s->nodes[head].tag == HT_APP) {
        if (!work_okay(s)) {
            return 0;
        }
        ++count;
        head = ht_deref(s, s->nodes[head].a);
    }
    if (head == HT_NONE) {
        return fail(s, "Invalid term spine");
    }
    HTerm predecessor = HT_NONE;
    if (s->nodes[head].tag == HT_NAT && strcmp(s->nodes[head].digits, "0")) {
        if (s->successor == HT_NONE) {
            return fail(s, "Natural successor symbol is not configured");
        }
        predecessor = increment(s, head, -1);
        head = ht_constant(s, s->successor, -1);
        if (predecessor == HT_NONE || head == HT_NONE) {
            return 0;
        }
        ++count;
    }
    HTerm *arguments = spine->few;
    if (count > sizeof(spine->few) / sizeof(*spine->few)) {
        arguments = count <= SIZE_MAX / sizeof(*arguments) ? malloc(count * sizeof(*arguments)) : NULL;
        if (!arguments) {
            return fail(s, "Term allocation failed");
        }
    }
    size_t at = count;
    for (HTerm node = top; s->nodes[node].tag == HT_APP; node = ht_deref(s, s->nodes[node].a)) {
        arguments[--at] = s->nodes[node].b;
    }
    if (predecessor != HT_NONE) {
        arguments[--at] = predecessor;
    }
    spine->head = head;
    spine->args = arguments;
    spine->count = count;
    return 1;
}

int ht_spine(HolTermStore *s, HTerm term, HTSpine *spine)
{
    *spine = (HTSpine) { HT_NONE, NULL, 0, { 0 } };
    if (!operation_begin(s)) {
        return 0;
    }
    int result = spine_view(s, term, spine);
    operation_end(s);
    return result;
}

void ht_spine_free(HTSpine *spine)
{
    if (spine->args != spine->few) {
        free(spine->args);
    }
    *spine = (HTSpine) { HT_NONE, NULL, 0, { 0 } };
}

/* The function parts are compared before the arguments, which wait in frames. */
static int equal(HolTermStore *s, HTerm left, HTerm right)
{
    size_t base = s->frame_count;
    int same = 1;
    while (same) {
        if (!work_okay(s)) {
            same = 0;
            break;
        }
        left = ht_deref(s, left);
        right = ht_deref(s, right);
        if (left != right) {
            TermNode a = s->nodes[left], b = s->nodes[right];
            if (a.tag != b.tag || (stable(a) && stable(b) && (a.scope != b.scope || a.open != b.open || a.mask != b.mask))) {
                same = 0;
                break;
            }
            if (a.tag == HT_APP) {
                if (!enter(s, a.b, 0, 0)) {
                    same = 0;
                    break;
                }
                s->frames[s->frame_count - 1].left = b.b;
                left = a.a;
                right = b.a;
                continue;
            }
            if (a.tag == HT_LAM) {
                left = a.a;
                right = b.a;
                continue;
            }
            if (a.tag == HT_VAR || a.tag == HT_NOMINAL) {
                same = a.uid == b.uid;
            } else if (a.tag == HT_CONST || a.tag == HT_INDEX) {
                same = a.a == b.a;
            } else if (a.tag == HT_NAT) {
                same = !strcmp(a.digits, b.digits);
            } else {
                same = a.tag == HT_WILD;
            }
        }
        if (!same || s->frame_count == base) {
            break;
        }
        Frame frame = s->frames[--s->frame_count];
        left = frame.term;
        right = frame.left;
    }
    s->frame_count = base;
    return same;
}

static int rigid(HolTermStore *s, HTerm term)
{
    TermNode n = s->nodes[ht_deref(s, term)];
    if (n.tag == HT_CONST && marked(s, n.a, MARK_OPAQUE)) {
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
        if (equal(s, term, terms[i])) {
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

/* 1 also when the store fails: the caller then finds the error. */
static int occurs(HolTermStore *s, HTerm variable, HTerm term)
{
    size_t base = s->frame_count;
    int found = 0;
    for (;;) {
        if (!work_okay(s)) {
            found = 1;
            break;
        }
        term = ht_deref(s, term);
        if (term == variable) {
            found = 1;
            break;
        }
        TermNode n = s->nodes[term];
        if (!stable(n) && n.tag == HT_APP) {
            if (!enter(s, n.b, 0, 0)) {
                found = 1;
                break;
            }
            term = n.a;
            continue;
        }
        if (!stable(n) && n.tag == HT_LAM) {
            term = n.a;
            continue;
        }
        if (s->frame_count == base) {
            break;
        }
        term = s->frames[--s->frame_count].term;
    }
    s->frame_count = base;
    return found;
}

static int lower_scopes(HolTermStore *s, HTerm term, size_t scope)
{
    size_t base = s->frame_count;
    int okay = 1;
    for (;;) {
        if (!work_okay(s)) {
            okay = 0;
            break;
        }
        term = ht_deref(s, term);
        TermNode n = s->nodes[term];
        if (!stable(n) && n.tag == HT_APP) {
            if (!enter(s, n.b, 0, 0)) {
                okay = 0;
                break;
            }
            term = n.a;
            continue;
        }
        if (!stable(n) && n.tag == HT_LAM) {
            term = n.a;
            continue;
        }
        if (n.tag == HT_VAR && n.scope > scope) {
            if (!trail_variable(s, term)) {
                okay = 0;
                break;
            }
            s->nodes[term].scope = scope;
        }
        if (s->frame_count == base) {
            break;
        }
        term = s->frames[--s->frame_count].term;
    }
    s->frame_count = base;
    return okay;
}

/* 1 also when the store fails: the caller then finds the error. */
static int index_free(HolTermStore *s, HTerm term, size_t index)
{
    size_t base = s->frame_count;
    int found = 0;
    for (;;) {
        if (!work_okay(s)) {
            found = 1;
            break;
        }
        term = ht_deref(s, term);
        TermNode n = s->nodes[term];
        if (!closed_below(n, index)) {
            if (stable(n) && index < 32 && (n.mask >> index & 1)) {
                found = 1;
                break;
            }
            if (n.tag == HT_APP) {
                if (!enter(s, n.b, index, 0)) {
                    found = 1;
                    break;
                }
                term = n.a;
                continue;
            }
            if (n.tag == HT_LAM) {
                term = n.a;
                ++index;
                continue;
            }
            if (n.tag == HT_INDEX && n.a == index) {
                found = 1;
                break;
            }
        }
        if (s->frame_count == base) {
            break;
        }
        Frame frame = s->frames[--s->frame_count];
        term = frame.term;
        index = frame.level;
    }
    s->frame_count = base;
    return found;
}

/* Stages of a frame: 0 not visited yet; 1 an application whose function is
    * being reduced; 2 its argument; 3 an abstraction whose body is. An eta step
    * visits the same frame again with the contracted term. */
static HTerm eta_reduce(HolTermStore *s, HTerm root)
{
    size_t base = s->frame_count;
    HTerm result = HT_NONE;
    if (root != HT_NONE && (s->nodes[ht_deref(s, root)].summary & (HS_STABLE | HS_ETA)) == (HS_STABLE | HS_ETA)) {
        return work_okay(s) ? ht_deref(s, root) : HT_NONE;
    }
    if (!enter(s, root, 0, 0)) {
        return HT_NONE;
    }
    while (s->frame_count > base) {
        Frame frame = s->frames[s->frame_count - 1];
        if (frame.stage == 0) {
            if (!work_okay(s)) {
                break;
            }
            HTerm term = ht_deref(s, frame.term);
            TermNode n = s->nodes[term];
            int settled = (n.summary & (HS_STABLE | HS_ETA)) == (HS_STABLE | HS_ETA);
            if (!settled && (n.tag == HT_APP || n.tag == HT_LAM)) {
                s->frames[s->frame_count - 1].term = term;
                s->frames[s->frame_count - 1].stage = n.tag == HT_APP ? 1 : 3;
                if (!enter(s, n.a, 0, 0)) {
                    break;
                }
                continue;
            }
            result = term;
        } else if (frame.stage == 1) {
            s->frames[s->frame_count - 1].left = result;
            s->frames[s->frame_count - 1].stage = 2;
            if (!enter(s, s->nodes[frame.term].b, 0, 0)) {
                break;
            }
            continue;
        } else if (frame.stage == 2) {
            TermNode n = s->nodes[frame.term];
            result = unchanged(s, frame.left, n.a) && unchanged(s, result, n.b) ? frame.term : ht_app(s, frame.left, result, n.meta);
        } else {
            TermNode n = s->nodes[frame.term], body = s->nodes[result];
            if (body.tag == HT_APP) {
                TermNode argument = s->nodes[ht_deref(s, body.b)];
                if (argument.tag == HT_INDEX && !argument.a && !index_free(s, body.a, 0)) {
                    HTerm reduced = remove_binder(s, body.a, 0);
                    if (reduced == HT_NONE) {
                        break;
                    }
                    s->frames[s->frame_count - 1].term = reduced;
                    s->frames[s->frame_count - 1].stage = 0;
                    continue;
                }
                if (s->error[0]) {
                    break;
                }
            }
            result = unchanged(s, result, n.a) ? frame.term : ht_lam(s, result, n.meta);
        }
        if (result == HT_NONE) {
            break;
        }
        --s->frame_count;
    }
    if (s->frame_count > base) {
        s->frame_count = base;
        return HT_NONE;
    }
    return result;
}

static int assign(HolTermStore *s, HTerm variable, HTerm value)
{
    value = eta_reduce(s, ht_normalize(s, value, HT_NF));
    if (value == HT_NONE) {
        return -1;
    }
    if (ht_deref(s, variable) == value) {
        return 1;
    }
    if (occurs(s, variable, value)) {
        return s->error[0] ? -1 : 0;
    }
    if (!lower_scopes(s, value, s->nodes[variable].scope) || !trail_variable(s, variable)) {
        return -1;
    }
    s->nodes[variable].a = value;
    ++s->changes;
    return 1;
}

/* Whether term is literally head applied to these arguments. A bound variable
    * in between does not count: building the value again removes it, so that a
    * value whose variables are all bound becomes stable. */
static int same_applications(const HolTermStore *s, HTerm term, HTerm head, const HTerm *arguments, size_t count)
{
    while (count) {
        TermNode n = s->nodes[term];
        if (n.tag != HT_APP || n.b != arguments[--count]) {
            return 0;
        }
        term = n.a;
    }
    return term == head;
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
        if (!push_term(s, result, shift(s, parameters[i], binders, 0))) {
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

/* A value whose parts are still being bound: an abstraction waiting for its
    * body, or a rigid head waiting for the arguments from next on. */
typedef struct {
    HTerm value, head;
    HTerm *args;
    size_t count, next;
    Terms results;
    int lambda;
    int64_t meta;
} Binding;

typedef struct { Binding *items; size_t count, capacity; } Bindings;

/* The value is an application or an atom in head normal form. A rigid head
    * leaves its arguments in *pending, to be bound next; without arguments, and
    * for a flexible head, *result is the bound value.
    * 2 means that a non-pattern equation must be delayed. */
static int bind_spine(HolTermStore *s, HTerm variable, HTerm value, const HTerm *parameters, size_t arity, const Words *outer, const Words *bound, Binding *pending, HTerm *result)
{
    HTSpine rhs = { 0 };
    Terms lhs = { 0 }, common = { 0 }, lhs_args = { 0 }, rhs_args = { 0 };
    Words hints = { 0 }, rhs_hints = { 0 };
    int status = -1;
    *pending = (Binding) { value, HT_NONE, NULL, 0, 0, { 0 }, 0, -1 };
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
            output_head = h.tag == HT_INDEX && h.a == lhs.count - index - 1 ? head : ht_index(s, lhs.count - index - 1);
        }
        pending->head = output_head;
        if (rhs.args != rhs.few) {
            pending->args = rhs.args;
            rhs.args = NULL;
        } else if (rhs.count) {
            pending->args = malloc(rhs.count * sizeof(*pending->args));
            if (!pending->args) {
                fail(s, "Term allocation failed");
                goto finish;
            }
            memcpy(pending->args, rhs.few, rhs.count * sizeof(*pending->args));
        }
        pending->count = rhs.count;
        *result = output_head;
        status = output_head == HT_NONE ? -1 : 1;
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

/* The value of the variable applied to the parameters: value with every
    * parameter and every binder of its own replaced by an index. The pending
    * parts are kept in an array, not on the C stack.
    * 2 means that a non-pattern equation must be delayed. */
static int bind_value(HolTermStore *s, HTerm variable, HTerm value, const HTerm *parameters, size_t arity, const Words *outer, Words *bound, HTerm *result)
{
    Bindings pending = { NULL, 0, 0 };
    size_t hints = bound->count;
    int status = 1, descending = 1;
    while (status == 1) {
        if (descending) {
            status = -1;
            if (!work_okay(s)) {
                break;
            }
            value = ht_normalize(s, value, HT_HNF);
            if (value == HT_NONE) {
                break;
            }
            TermNode n = s->nodes[value];
            /* nothing below is a parameter, a variable or out of the variable's scope */
            if ((stable(n) && n.scope <= s->nodes[variable].scope && closed_below(n, bound->count)) || n.tag == HT_NAT) {
                *result = value;
                status = 1;
                descending = 0;
                continue;
            }
            Binding part = { value, HT_NONE, NULL, 0, 0, { 0 }, 1, n.meta };
            if (n.tag != HT_LAM) {
                status = bind_spine(s, variable, value, parameters, arity, outer, bound, &part, result);
                if (status != 1 || !part.count) {
                    free(part.args);
                    descending = 0;
                    continue;
                }
                status = -1;
            }
            if ((part.lambda && !push_word(s, bound, n.meta)) || !reserve(s, (void **) &pending.items, &pending.capacity, pending.count + 1, sizeof(*pending.items))) {
                free(part.args);
                break;
            }
            pending.items[pending.count++] = part;
            value = part.lambda ? n.a : part.args[0];
            status = 1;
        } else if (!pending.count) {
            break;
        } else {
            Binding *top = &pending.items[pending.count - 1];
            if (top->lambda) {
                --bound->count;
                *result = *result == s->nodes[top->value].a ? top->value : ht_lam(s, *result, top->meta);
            } else if (!push_term(s, &top->results, *result)) {
                status = -1;
                break;
            } else if (++top->next < top->count) {
                value = top->args[top->next];
                descending = 1;
                continue;
            } else {
                *result = same_applications(s, top->value, top->head, top->results.items, top->results.count) ? top->value : applications(s, top->head, top->results.items, top->results.count);
                free(top->args);
                free(top->results.items);
            }
            --pending.count;
            if (*result == HT_NONE) {
                status = -1;
            }
        }
    }
    while (pending.count) {
        Binding *top = &pending.items[--pending.count];
        free(top->args);
        free(top->results.items);
    }
    free(pending.items);
    bound->count = hints;
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
            if (equal(s, lhs.items[i], body_spine.args[i])) {
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
        HTerm replacement = HT_NONE;
        status = bind_value(s, variable, rhs, normalized.items, normalized.count, outer, &bound, &replacement);
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

static int add_equation(HolTermStore *s, Equations *equations, HTerm left, HTerm right)
{
    if (left == HT_NONE || right == HT_NONE || !reserve(s, (void **) &equations->items, &equations->capacity, equations->count + 1, sizeof(*equations->items))) {
        return 0;
    }
    equations->items[equations->count++] = (Equation) { left, right };
    return 1;
}

/* known is the value of s->changes at which left and right were in normal
    * form; they are still in normal form while nothing has been bound since. The
    * body of an abstraction and the first argument of a rigid term are solved
    * next; the other arguments wait in s->pairs, each with the number of binders
    * above it, so neither a long list nor a deep argument nests. */
static int solve_pair(HolTermStore *s, HTerm left, HTerm right, Words *outer, Equations *delayed)
{
    HTSpine lhs = { 0 }, rhs = { 0 };
    size_t base = s->pair_count, binders = outer->count;
    uint64_t known = 0;
    int reduced = 0, status;
    for (;;) {
        for (;;) {
            status = -1;
            if (!work_okay(s)) {
                break;
            }
            if (reduced && s->changes == known) {
                left = ht_deref(s, left);
                right = ht_deref(s, right);
            } else {
                left = ht_normalize(s, left, HT_NF);
                right = ht_normalize(s, right, HT_NF);
                known = s->changes;
            }
            reduced = 1;
            if (left == HT_NONE || right == HT_NONE) {
                break;
            }
            if (left == right) {
                status = 1;
                break;
            }
            TermNode l = s->nodes[left], r = s->nodes[right];
            if (normal(l) && normal(r)) {
                status = equal(s, left, right);
                break;
            }
            if (l.tag == HT_LAM && r.tag == HT_LAM) {
                if (!push_word(s, outer, l.meta)) {
                    break;
                }
                left = l.a;
                right = r.a;
                continue;
            }
            ht_spine_free(&lhs);
            ht_spine_free(&rhs);
            if (!spine_view(s, left, &lhs) || !spine_view(s, right, &rhs)) {
                break;
            }
            HTerm lh = ht_deref(s, lhs.head), rh = ht_deref(s, rhs.head);
            if ((l.tag == HT_LAM && rigid(s, rh)) || (r.tag == HT_LAM && rigid(s, lh))) {
                int left_lambda = l.tag == HT_LAM;
                HTerm expansion = shift(s, left_lambda ? right : left, 1, 0);
                HTerm index = ht_index(s, 0);
                expansion = ht_app(s, expansion, index, -1);
                if (expansion == HT_NONE || !push_word(s, outer, left_lambda ? l.meta : r.meta)) {
                    break;
                }
                left = left_lambda ? l.a : expansion;
                right = left_lambda ? expansion : r.a;
                continue;
            }
            if (rigid(s, lh) && rigid(s, rh)) {
                if (!equal(s, lh, rh) || lhs.count != rhs.count) {
                    status = 0;
                    break;
                }
                status = 1;
                if (!lhs.count) {
                    break;
                }
                if (lhs.count - 1 > SIZE_MAX - s->pair_count || !reserve(s, (void **) &s->pairs, &s->pair_capacity, s->pair_count + lhs.count - 1, sizeof(*s->pairs))) {
                    status = -1;
                    break;
                }
                for (size_t i = lhs.count; i > 1; --i) {
                    s->pairs[s->pair_count++] = (Pair) { lhs.args[i - 1], rhs.args[i - 1], outer->count, known };
                }
                left = lhs.args[0];
                right = rhs.args[0];
                continue;
            }
            if (equal(s, left, right)) {
                status = 1;
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
            break;
        }
        if (status != 1 || s->error[0] || s->pair_count == base) {
            break;
        }
        Pair next = s->pairs[--s->pair_count];
        left = next.left;
        right = next.right;
        known = next.known;
        outer->count = next.binders;
    }
    s->pair_count = base;
    outer->count = binders;
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
    /* The buffers of the store are borrowed unless a unification is running. */
    int borrowed = !s->unifying;
    Equations input = { 0 }, output = { 0 };
    Words outer = { 0 };
    if (borrowed) {
        input = s->solving;
        output = s->delayed;
        outer = s->binders;
        input.count = 0;
        output.count = 0;
        outer.count = 0;
        s->unifying = 1;
    }
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
            status = solve_pair(s, input.items[i].left, input.items[i].right, &outer, &output);
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
    if (borrowed) {
        s->solving = input;
        s->delayed = output;
        s->binders = outer;
        s->unifying = 0;
    } else {
        free(input.items);
        free(output.items);
        free(outer.items);
    }
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

/* 1: every variable and nominal of the term is within scope and every loose
    * index is below binders; 0: not so; -1: store error. */
static int assignment_scope(HolTermStore *s, HTerm term, size_t scope, size_t binders)
{
    size_t base = s->frame_count;
    int status = 1;
    for (;;) {
        if (!work_okay(s)) {
            status = -1;
            break;
        }
        term = ht_deref(s, term);
        if (term == HT_NONE) {
            fail(s, "Invalid checked assignment term");
            status = -1;
            break;
        }
        TermNode n = s->nodes[term];
        if (stable(n) && n.open != OPEN_UNKNOWN) {
            status = n.scope <= scope && n.open <= binders;
        } else if (n.tag == HT_APP) {
            if (!enter(s, n.b, binders, 0)) {
                status = -1;
                break;
            }
            term = n.a;
            continue;
        } else if (n.tag == HT_LAM) {
            term = n.a;
            ++binders;
            continue;
        } else if (n.tag == HT_VAR || n.tag == HT_NOMINAL) {
            status = n.scope <= scope;
        } else if (n.tag == HT_INDEX) {
            status = n.a < binders;
        }
        if (status != 1 || s->frame_count == base) {
            break;
        }
        Frame frame = s->frames[--s->frame_count];
        term = frame.term;
        binders = frame.level;
    }
    s->frame_count = base;
    return status;
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
                status = assignment_scope(s, value, s->nodes[target].scope, 0);
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

/* One term without subterms; HT_NONE with the store in error. */
static HTerm import_leaf(HolTermStore *s, int64_t tag, const int64_t *words, size_t count, size_t *offset, int restoring)
{
    int64_t a, b, c, d;
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
                s->nodes[previous].pinned = 1;
                return previous;
            }
            if (!restoring && identity_retired(s, (uint64_t) a)) {
                fail(s, "Term wire refers to an expired identity");
                return HT_NONE;
            }
            HTerm created = identity_node(s, (int) tag, (uint64_t) a, (size_t) b, (int) c, d, restoring);
            if (created != HT_NONE) {
                s->nodes[created].pinned = 1;
            }
            return created;
        }
        case HT_CONST:
            if (!read_word(s, words, count, offset, &a) || !read_word(s, words, count, offset, &b) || a < 0 || (uint64_t) a > SIZE_MAX || b < -1) {
                fail(s, "Invalid constant wire");
                return HT_NONE;
            }
            return ht_constant(s, (size_t) a, b);
        case HT_INDEX:
            if (!read_word(s, words, count, offset, &a) || a < 0 || (uint64_t) a > SIZE_MAX) {
                fail(s, "Invalid bound variable wire");
                return HT_NONE;
            }
            return ht_index(s, (size_t) a);
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

/* A frame is an application or an abstraction whose parts are still being
    * read: stage 0 an abstraction, 1 an application without its function, 2 one
    * with it (term). level is the annotation plus one. */
static HTerm import_term(HolTermStore *s, const int64_t *words, size_t count, size_t *offset, int restoring)
{
    size_t base = s->frame_count;
    HTerm value = HT_NONE;
    for (;;) {
        int64_t tag, meta;
        if (!work_okay(s) || !read_word(s, words, count, offset, &tag)) {
            break;
        }
        if (tag == HT_APP || tag == HT_LAM) {
            if (!read_word(s, words, count, offset, &meta) || meta < -1) {
                fail(s, tag == HT_APP ? "Invalid application wire" : "Invalid lambda wire");
                break;
            }
            if (!reserve(s, (void **) &s->frames, &s->frame_capacity, s->frame_count + 1, sizeof(*s->frames))) {
                break;
            }
            s->frames[s->frame_count++] = (Frame) { HT_NONE, HT_NONE, (size_t) (meta + 1), tag == HT_APP, 0 };
            continue;
        }
        value = import_leaf(s, tag, words, count, offset, restoring);
        while (value != HT_NONE && s->frame_count > base && s->frames[s->frame_count - 1].stage != 1) {
            Frame frame = s->frames[--s->frame_count];
            int64_t annotation = (int64_t) frame.level - 1;
            value = frame.stage ? ht_app(s, frame.term, value, annotation) : ht_lam(s, value, annotation);
        }
        if (value == HT_NONE || s->frame_count == base) {
            break;
        }
        s->frames[s->frame_count - 1].term = value;
        s->frames[s->frame_count - 1].stage = 2;
        value = HT_NONE;
    }
    s->frame_count = base;
    return s->error[0] ? HT_NONE : value;
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
    HTerm term = import_term(s, words, count, offset, restoring);
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

/* The wire is the term in prefix order: the frames hold the subterms that
    * are still to be written, the next one on top. */
static int export_term(HolTermStore *s, HTerm root, Words *words)
{
    size_t base = s->frame_count;
    int written = enter(s, root, 0, 0);
    while (written && s->frame_count > base) {
        HTerm term = ht_deref(s, s->frames[--s->frame_count].term);
        if (!work_okay(s)) {
            written = 0;
            break;
        }
        if (term == HT_NONE) {
            written = fail(s, "Invalid term export reference");
            break;
        }
        TermNode n = s->nodes[term];
        written = push_word(s, words, n.tag);
        switch (written ? n.tag : -1) {
            case -1:
                break;
            case HT_VAR:
                s->nodes[term].pinned = 1;
                written = push_word(s, words, (int64_t) n.uid) && push_word(s, words, (int64_t) n.scope) && push_word(s, words, n.is_type) && push_word(s, words, n.meta);
                break;
            case HT_CONST:
                written = push_word(s, words, (int64_t) n.a) && push_word(s, words, n.meta);
                break;
            case HT_APP:
                written = push_word(s, words, n.meta) && enter(s, n.b, 0, 0) && enter(s, n.a, 0, 0);
                break;
            case HT_INDEX:
                written = push_word(s, words, (int64_t) n.a);
                break;
            case HT_LAM:
                written = push_word(s, words, n.meta) && enter(s, n.a, 0, 0);
                break;
            case HT_NOMINAL:
                s->nodes[term].pinned = 1;
                written = push_word(s, words, (int64_t) n.uid) && push_word(s, words, (int64_t) n.scope) && push_word(s, words, n.meta);
                break;
            case HT_NAT: {
                size_t length = strlen(n.digits);
                if (length > INT64_MAX || !push_word(s, words, (int64_t) length)) {
                    written = fail(s, "Natural export length overflow");
                }
                for (size_t i = 0; written && i < length; ++i) {
                    written = push_word(s, words, n.digits[i]);
                }
                break;
            }
            case HT_WILD:
                break;
            default:
                written = fail(s, "Invalid term export tag");
                break;
        }
    }
    s->frame_count = base;
    return written;
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
    if (term == HT_NONE || !export_term(s, term, &output)) {
        free(output.items);
        operation_end(s);
        return 0;
    }
    *words = output.items;
    *count = output.count;
    operation_end(s);
    return 1;
}

void ht_pin(HolTermStore *s, HTerm term)
{
    if (s && term < s->count) {
        s->nodes[term].pinned = 1;
    }
}

/* The nodes below base are sealed and kept: they are live, stay where they
    * are, and refer to nothing above base. live and forward describe the nodes
    * from base on. */
struct HTCollection {
    HolTermStore *store;
    unsigned char *live;
    size_t *forward, *trail_forward;
    HTerm *stack;
    size_t base, stack_count, stack_capacity;
    int failed;
};

static int collected_live(const HTCollection *c, HTerm term)
{
    return term < c->base || c->live[term - c->base];
}

/* The new place of a live node, or of a heap position up to the count. */
static size_t collected_at(const HTCollection *c, size_t at)
{
    return at < c->base ? at : c->forward[at - c->base];
}

void ht_collect_mark(HTCollection *c, HTerm term)
{
    HolTermStore *s = c->store;
    size_t base = c->stack_count;
    for (;;) {
        while (term < s->count && !collected_live(c, term)) {
            c->live[term - c->base] = 1;
            TermNode n = s->nodes[term];
            if (n.tag == HT_APP) {
                if (c->stack_count == c->stack_capacity) {
                    size_t capacity = c->stack_capacity ? c->stack_capacity * 2 : 256;
                    HTerm *grown = capacity > c->stack_capacity && capacity <= SIZE_MAX / sizeof(*grown) ? realloc(c->stack, capacity * sizeof(*grown)) : NULL;
                    if (!grown) {
                        c->failed = 1;
                        c->stack_count = base;
                        return;
                    }
                    c->stack = grown;
                    c->stack_capacity = capacity;
                }
                c->stack[c->stack_count++] = n.b;
                term = n.a;
            } else if (n.tag == HT_LAM || n.tag == HT_VAR) {
                term = n.a;
            } else {
                break;
            }
        }
        if (c->stack_count == base) {
            return;
        }
        term = c->stack[--c->stack_count];
    }
}

HTerm ht_collect_term(const HTCollection *c, HTerm term)
{
    return term < c->store->count && collected_live(c, term) ? collected_at(c, term) : HT_NONE;
}

size_t ht_collect_heap(const HTCollection *c, size_t heap)
{
    return collected_at(c, heap < c->store->count ? heap : c->store->count);
}

size_t ht_collect_trail(const HTCollection *c, size_t trail)
{
    return c->trail_forward[trail < c->store->trail_count ? trail : c->store->trail_count];
}

int ht_collect(HolTermStore *s, size_t keep, const HTCollector *collector, void *context)
{
    if (!s || s->error[0] || s->operations || !collector || keep > s->count) {
        return 0;
    }
    if (s->sealed > keep) {
        s->sealed = keep;
    }
    HTCollection c = { s, NULL, NULL, NULL, NULL, s->sealed, 0, 0, 0 };
    size_t span = s->count - c.base;
    c.live = calloc(span ? span : 1, 1);
    c.forward = span < SIZE_MAX / sizeof(*c.forward) ? malloc((span + 1) * sizeof(*c.forward)) : NULL;
    c.trail_forward = s->trail_count < SIZE_MAX / sizeof(*c.trail_forward) ? malloc((s->trail_count + 1) * sizeof(*c.trail_forward)) : NULL;
    size_t expired_capacity = s->identity_count, expired_count = 0;
    uint64_t *expired = malloc((expired_capacity ? expired_capacity : 1) * sizeof(*expired));
    int sorted = 1;
    if (!c.live || !c.forward || !c.trail_forward || !expired) {
        c.failed = 1;
    }
    for (size_t i = c.base; !c.failed && i < s->count; ++i) {
        if (i < keep || s->nodes[i].pinned) {
            ht_collect_mark(&c, i);
        }
    }
    for (size_t i = 0; !c.failed && i < s->pending_count; ++i) {
        ht_collect_mark(&c, s->pending[i].left);
        ht_collect_mark(&c, s->pending[i].right);
    }
    if (!c.failed && collector->mark) {
        collector->mark(&c, context);
    }
    /* A binding is undone only for a variable that some root still reaches. */
    for (int changed = 1; !c.failed && changed;) {
        changed = 0;
        for (size_t i = 0; !c.failed && i < s->trail_count; ++i) {
            HTerm binding = s->trail[i].binding;
            if (collected_live(&c, s->trail[i].variable) && binding != HT_NONE && !collected_live(&c, binding)) {
                ht_collect_mark(&c, binding);
                changed = 1;
            }
        }
    }
    if (c.failed) {
        free(c.live);
        free(c.forward);
        free(c.trail_forward);
        free(c.stack);
        free(expired);
        return 0;
    }
    size_t kept = c.base;
    for (size_t i = 0; i < span; ++i) {
        c.forward[i] = kept;
        kept += c.live[i];
    }
    c.forward[span] = kept;
    size_t entries = 0;
    for (size_t i = 0; i < s->trail_count; ++i) {
        c.trail_forward[i] = entries;
        entries += collected_live(&c, s->trail[i].variable);
    }
    c.trail_forward[s->trail_count] = entries;
    for (size_t i = c.base; i < s->count; ++i) {
        TermNode n = s->nodes[i];
        if (!c.live[i - c.base]) {
            if ((n.tag == HT_VAR || n.tag == HT_NOMINAL) && expired_count < expired_capacity) {
                sorted = sorted && (!expired_count || expired[expired_count - 1] < n.uid);
                expired[expired_count++] = n.uid;
                remove_identity(s, n.uid, 0);
            }
            free(n.digits);
            continue;
        }
        if (n.tag == HT_APP) {
            n.a = collected_at(&c, n.a);
            n.b = collected_at(&c, n.b);
        } else if (n.tag == HT_LAM || (n.tag == HT_VAR && n.a != HT_NONE)) {
            n.a = collected_at(&c, n.a);
        }
        s->nodes[c.forward[i - c.base]] = n;
    }
    if (!sorted) {
        qsort(expired, expired_count, sizeof(*expired), ascending);
    }
    retire_sorted(s, expired, expired_count);
    free(expired);
    for (size_t i = 0; i < s->identity_capacity; ++i) {
        if (s->identities[i].uid != UID_EMPTY) {
            s->identities[i].term = collected_at(&c, s->identities[i].term);
        }
    }
    for (size_t i = 0; i < s->trail_count; ++i) {
        Trail entry = s->trail[i];
        if (collected_live(&c, entry.variable)) {
            entry.variable = collected_at(&c, entry.variable);
            entry.binding = entry.binding == HT_NONE ? HT_NONE : collected_at(&c, entry.binding);
            s->trail[c.trail_forward[i]] = entry;
        }
    }
    for (size_t i = 0; i < s->pending_count; ++i) {
        s->pending[i].left = collected_at(&c, s->pending[i].left);
        s->pending[i].right = collected_at(&c, s->pending[i].right);
    }
    if (collector->relocate) {
        collector->relocate(&c, context);
    }
    s->count = kept;
    s->trail_count = entries;
    if (s->capacity / 4 > s->count && s->capacity > 1024) {
        size_t capacity = s->count * 2 > 1024 ? s->count * 2 : 1024;
        TermNode *smaller = realloc(s->nodes, capacity * sizeof(*smaller));
        if (smaller) {
            s->nodes = smaller;
            s->capacity = capacity;
        }
    }
    /* The table keeps the size that the identities needed since the previous
        * collection: a run that creates as many again does not grow it again. */
    size_t peak = s->identity_peak;
    s->identity_peak = s->identity_count;
    if (s->identity_capacity / 8 > peak && s->identity_capacity > 64) {
        size_t capacity = 64;
        while (capacity / 4 < peak) {
            capacity *= 2;
        }
        rehash_identities(s, capacity);
    }
    free(c.live);
    free(c.forward);
    free(c.trail_forward);
    free(c.stack);
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
    copy->sealed = source->sealed;
    copy->work_limit = source->work_limit;
    if (source->mark_count) {
        if (!reserve(copy, (void **) &copy->marks, &copy->mark_capacity, source->mark_count, sizeof(*copy->marks))) {
            ht_destroy(copy);
            return NULL;
        }
        memcpy(copy->marks, source->marks, source->mark_count);
        copy->mark_count = source->mark_count;
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
    if (source->retired_count) {
        if (!reserve(copy, (void **) &copy->retired, &copy->retired_capacity, source->retired_count, sizeof(*copy->retired))) {
            ht_destroy(copy);
            return NULL;
        }
        memcpy(copy->retired, source->retired, source->retired_count * sizeof(*copy->retired));
        copy->retired_count = source->retired_count;
    }
    for (size_t i = 0; i < source->identity_capacity; ++i) {
        Identity entry = source->identities[i];
        if (entry.uid != UID_EMPTY && !insert_identity(copy, entry.uid, entry.term, 1)) {
            ht_destroy(copy);
            return NULL;
        }
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

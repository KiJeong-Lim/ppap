#ifndef HOL_V1_TERM_H
#define HOL_V1_TERM_H

#include <stddef.h>
#include <stdint.h>

#define HT_NONE SIZE_MAX

typedef size_t HTerm;
typedef struct HolTermStore HolTermStore;

enum HTTag { HT_VAR, HT_CONST, HT_APP, HT_INDEX, HT_LAM, HT_NOMINAL, HT_NAT, HT_WILD };
enum HTNormalForm { HT_WHNF, HT_HNF, HT_NF };

typedef struct {
    int tag;
    HTerm a, b;
    uint64_t uid;
    size_t symbol, scope;
    int is_type;
    int64_t meta;
    const char *digits;
} HTView;

typedef struct {
    size_t heap, trail, pending, pending_head;
} HTCheckpoint;

/* A few arguments are kept in the spine itself, so a spine is not copied:
    * args may point into it. */
typedef struct {
    HTerm head;
    HTerm *args;
    size_t count;
    HTerm few[6];
} HTSpine;

HolTermStore *ht_create(void);
HolTermStore *ht_clone(const HolTermStore *source);
void ht_destroy(HolTermStore *store);
const char *ht_error(const HolTermStore *store);
size_t ht_heap_count(const HolTermStore *store);
HTCheckpoint ht_checkpoint(const HolTermStore *store);
int ht_restore(HolTermStore *store, HTCheckpoint checkpoint);
/* The state between two runs: the first heap nodes stay, every binding is
    * undone, no disagreement is pending, and the identities from next_uid on, the
    * marks of the symbols from symbols on and the work limit are forgotten. The
    * caller keeps no node and no identity above those bounds. 0: store error. */
int ht_reset(HolTermStore *store, size_t heap, uint64_t next_uid, size_t symbols);
/* Seals the nodes that precede the first variable: no binding can make them
    * refer to a younger node, so a collection that keeps them neither visits nor
    * moves them. Returns their number; ht_sealed reads it. */
size_t ht_seal(HolTermStore *store);
size_t ht_sealed(const HolTermStore *store);
uint64_t ht_next_uid(const HolTermStore *store);
/* Advancing the fresh-UID frontier does not retire never-materialized gaps. */
int ht_advance_uid(HolTermStore *store, uint64_t next_uid);
/* Preserve retirement when replacing a live store with an older snapshot. */
int ht_preserve_identity_history(HolTermStore *restored, const HolTermStore *live);
void ht_set_successor(HolTermStore *store, size_t symbol);
int ht_set_opaque_symbol(HolTermStore *store, size_t symbol);
/* An arithmetic symbol is one that the host evaluates. ht_mentions_arithmetic
    * is 1 when the term, as bound now, contains such a symbol, the successor or
    * an opaque symbol; 0 when it contains none; -1 on a store error. */
int ht_set_arithmetic_symbol(HolTermStore *store, size_t symbol);
int ht_mentions_arithmetic(HolTermStore *store, HTerm term);
/* Positive per-operation node-visit bound; nested operations share the budget. */
int ht_set_work_limit(HolTermStore *store, uint64_t visits);
uint64_t ht_work_limit(const HolTermStore *store);

HTerm ht_var(HolTermStore *store, size_t scope, int is_type, int64_t meta);
HTerm ht_nominal(HolTermStore *store, size_t scope, int64_t meta);
HTerm ht_constant(HolTermStore *store, size_t symbol, int64_t meta);
HTerm ht_nat(HolTermStore *store, const char *digits);
HTerm ht_index(HolTermStore *store, size_t index);
HTerm ht_lam(HolTermStore *store, HTerm body, int64_t meta);
HTerm ht_app(HolTermStore *store, HTerm function, HTerm argument, int64_t meta);
HTerm ht_wildcard(HolTermStore *store);
HTerm ht_lookup_uid(const HolTermStore *store, uint64_t uid);
HTerm ht_deref(const HolTermStore *store, HTerm term);
HTView ht_view(const HolTermStore *store, HTerm term);
HTerm ht_normalize(HolTermStore *store, HTerm term, enum HTNormalForm form);
HTerm ht_apply(HolTermStore *store, HTerm function, HTerm argument);
/* Replaces the indices of count enclosing binders at once: index i of body
    * denotes values[count - 1 - i]. Every value is a variable or a nominal. */
HTerm ht_instantiate(HolTermStore *store, HTerm body, const HTerm *values, size_t count);
int ht_spine(HolTermStore *store, HTerm term, HTSpine *spine);
void ht_spine_free(HTSpine *spine);

/* Unification is atomic on logical failure and preserves unresolved equations.
    * -1: store error; 0: incompatible terms; 1: solved or retained disagreement. */
int ht_unify(HolTermStore *store, HTerm left, HTerm right);
int ht_retry(HolTermStore *store);
/* Host type-checked debugger assignment: strict scope/occurs checks, permitting
    * opaque goal values. Existing bindings are checked by ordinary unification. */
int ht_assign_checked(HolTermStore *store, HTerm variable, HTerm value);
size_t ht_pending_count(const HolTermStore *store);
int ht_pending(const HolTermStore *store, size_t index, HTerm *left, HTerm *right);

/* Prefix term wire, matching HTTag. VAR: uid,scope,is_type,meta;
    * CONST: symbol,meta; APP: meta,fn,arg; INDEX: index; LAM: meta,body;
    * NOMINAL: uid,scope,meta; NAT: byte-count,decimal ASCII; WILD: no payload.
    * Import consumes one term, advances *offset, and reuses live UID identities.
    * Export allocates *words; caller releases it with free(). */
/* Export and import pin the identities they name: the host may name a pinned
    * variable or nominal again, so a collection keeps it. */
HTerm ht_import(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
/* Authorized snapshot/persistent-assignment replay may restore retired UIDs. */
HTerm ht_import_restored(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
int ht_export(HolTermStore *store, HTerm term, int64_t **words, size_t *count);

void ht_pin(HolTermStore *store, HTerm term);

/* Order-preserving compaction. The first keep nodes, pinned identities, every
    * disagreement and whatever mark names stay; a trailed binding stays with its
    * variable. The cost does not depend on the sealed nodes among the first keep. relocate then rewrites the caller's terms and checkpoint
    * positions before the old numbering is dropped. An unreachable identity is
    * retired. 0 means that nothing was changed: temporary memory was missing. */
typedef struct HTCollection HTCollection;
typedef struct {
    void (*mark)(HTCollection *collection, void *context);
    void (*relocate)(const HTCollection *collection, void *context);
} HTCollector;
void ht_collect_mark(HTCollection *collection, HTerm term);
HTerm ht_collect_term(const HTCollection *collection, HTerm term);
size_t ht_collect_heap(const HTCollection *collection, size_t heap);
size_t ht_collect_trail(const HTCollection *collection, size_t trail);
int ht_collect(HolTermStore *store, size_t keep, const HTCollector *collector, void *context);

#endif

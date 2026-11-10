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

typedef struct {
    HTerm head;
    HTerm *args;
    size_t count;
} HTSpine;

HolTermStore *ht_create(void);
HolTermStore *ht_clone(const HolTermStore *source);
void ht_destroy(HolTermStore *store);
const char *ht_error(const HolTermStore *store);
size_t ht_heap_count(const HolTermStore *store);
HTCheckpoint ht_checkpoint(const HolTermStore *store);
int ht_restore(HolTermStore *store, HTCheckpoint checkpoint);
uint64_t ht_next_uid(const HolTermStore *store);
/* Advancing the fresh-UID frontier does not retire never-materialized gaps. */
int ht_advance_uid(HolTermStore *store, uint64_t next_uid);
/* Preserve retirement when replacing a live store with an older snapshot. */
int ht_preserve_identity_history(HolTermStore *restored, const HolTermStore *live);
void ht_set_successor(HolTermStore *store, size_t symbol);
int ht_set_opaque_symbol(HolTermStore *store, size_t symbol);
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
HTerm ht_import(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
/* Authorized snapshot/persistent-assignment replay may restore retired UIDs. */
HTerm ht_import_restored(HolTermStore *store, const int64_t *words, size_t count, size_t *offset);
int ht_export(HolTermStore *store, HTerm term, int64_t **words, size_t *count);

#endif

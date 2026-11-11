#include "term.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static size_t failure_index, allocation_count, largest_allocation;
static int allocation_testing;

void *__real_malloc(size_t count);
void *__real_calloc(size_t count, size_t width);
void *__real_realloc(void *old, size_t count);

static int allocation_fails(void)
{
    return allocation_testing && ++allocation_count == failure_index;
}

void *__wrap_malloc(size_t count)
{
    if (count > largest_allocation) largest_allocation = count;
    return allocation_fails() ? NULL : __real_malloc(count);
}

void *__wrap_calloc(size_t count, size_t width)
{
    if (width && count <= SIZE_MAX / width && count * width > largest_allocation) largest_allocation = count * width;
    return allocation_fails() ? NULL : __real_calloc(count, width);
}

void *__wrap_realloc(void *old, size_t count)
{
    if (count > largest_allocation) largest_allocation = count;
    return allocation_fails() ? NULL : __real_realloc(old, count);
}

static HolTermStore *store(void)
{
    HolTermStore *s = ht_create();
    assert(s);
    ht_set_successor(s, 0);
    return s;
}

static HTerm app(HolTermStore *s, HTerm f, HTerm a)
{
    HTerm result = ht_app(s, f, a, -1);
    assert(result != HT_NONE);
    return result;
}

static HTView normal(HolTermStore *s, HTerm term)
{
    HTerm result = ht_normalize(s, term, HT_NF);
    if (result == HT_NONE) {
        fprintf(stderr, "%s\n", ht_error(s));
    }
    assert(result != HT_NONE);
    return ht_view(s, result);
}

static void beta_capture(void)
{
    HolTermStore *s = store();
    HTerm lambda = ht_lam(s, ht_lam(s, ht_index(s, 1), 12), 11);
    HTerm result = ht_apply(s, lambda, ht_index(s, 0));
    HTView n = normal(s, result);
    assert(n.tag == HT_LAM && n.meta == 12);
    HTView body = normal(s, n.a);
    assert(body.tag == HT_INDEX && body.a == 1);
    HTerm x = ht_var(s, 0, 0, 20);
    HTerm f = ht_constant(s, 8, -1);
    HTerm eta = ht_lam(s, app(s, f, ht_index(s, 0)), 15);
    assert(ht_unify(s, x, eta) == 1);
    assert(normal(s, x).tag == HT_CONST && normal(s, x).symbol == 8);
    ht_destroy(s);
    puts("PASS beta_capture_and_eta");
}

static void naturals(void)
{
    HolTermStore *s = store();
    HTerm successor = ht_constant(s, 0, -1);
    HTerm x = ht_var(s, 0, 0, -1);
    HTerm huge = ht_nat(s, "100000000000000000000000000000000000000000000000000");
    assert(ht_unify(s, app(s, successor, x), huge) == 1);
    HTView value = normal(s, x);
    assert(value.tag == HT_NAT && !strcmp(value.digits, "99999999999999999999999999999999999999999999999999"));
    HTerm incremented = app(s, successor, x);
    assert(normal(s, incremented).tag == HT_NAT);
    assert(ht_unify(s, incremented, huge) == 1);
    HTerm y = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, app(s, successor, y), ht_nat(s, "0")) == 0);
    assert(normal(s, y).tag == HT_VAR);
    assert(ht_unify(s, ht_nat(s, "0007"), ht_nat(s, "7")) == 1);
    ht_destroy(s);
    puts("PASS big_natural_successor");
}

static void scope_and_rollback(void)
{
    HolTermStore *s = store();
    HTerm x = ht_var(s, 0, 0, -1);
    HTerm rigid = ht_nominal(s, 1, 1);
    assert(ht_unify(s, x, rigid) == 0);
    assert(normal(s, x).tag == HT_VAR);
    HTCheckpoint saved = ht_checkpoint(s);
    HTerm y = ht_var(s, 1, 0, -1);
    uint64_t abandoned = ht_view(s, y).uid;
    assert(ht_unify(s, x, y) == 1);
    assert(normal(s, x).scope == 0 && normal(s, y).scope == 0);
    assert(ht_restore(s, saved));
    assert(normal(s, x).tag == HT_VAR && ht_view(s, x).a == HT_NONE);
    HTerm z = ht_var(s, 0, 0, -1);
    assert(ht_view(s, z).uid > abandoned && ht_lookup_uid(s, abandoned) == HT_NONE);
    HTerm f = ht_constant(s, 7, -1);
    assert(ht_unify(s, z, app(s, f, z)) == 0);
    assert(ht_view(s, z).a == HT_NONE);
    ht_destroy(s);
    puts("PASS scope_occurs_and_rollback");
}

static void lambda_pruning(void)
{
    HolTermStore *s = store();
    HTerm x = ht_var(s, 0, 0, -1), y = ht_var(s, 0, 0, -1), z = ht_var(s, 0, 0, -1);
    HTerm f = ht_constant(s, 7, -1);
    HTerm c = ht_nominal(s, 1, 11), d = ht_nominal(s, 2, 12);
    HTerm rhs = app(s, app(s, f, app(s, app(s, y, c), d)), app(s, app(s, z, c), c));
    assert(ht_unify(s, app(s, x, c), rhs) == 1);
    assert(ht_pending_count(s) == 0);
    HTView nx = normal(s, x), ny = normal(s, y), nz = normal(s, z);
    assert(nx.tag == HT_LAM && nx.meta == 11);
    assert(ny.tag == HT_LAM && normal(s, ny.a).tag == HT_LAM);
    assert(nz.tag == HT_VAR);
    HTerm e = ht_nominal(s, 3, 13);
    assert(ht_unify(s, app(s, app(s, y, c), d), app(s, app(s, y, c), e)) == 1);
    ht_destroy(s);
    puts("PASS lbeta_flex_flex_and_duplicate_pruning");
}

static void same_head_pruning(void)
{
    HolTermStore *s = store();
    HTerm f = ht_var(s, 0, 0, -1);
    HTerm a = ht_nominal(s, 1, 10), b = ht_nominal(s, 2, 11), c = ht_nominal(s, 3, 12);
    assert(ht_unify(s, app(s, app(s, f, a), b), app(s, app(s, f, a), c)) == 1);
    assert(ht_pending_count(s) == 0);
    HTView n = normal(s, f);
    assert(n.tag == HT_LAM);
    n = normal(s, n.a);
    assert(n.tag == HT_LAM);
    n = normal(s, n.a);
    assert(n.tag == HT_APP && normal(s, n.b).tag == HT_INDEX && normal(s, n.b).a == 1);
    ht_destroy(s);
    puts("PASS same_head_pruning");
}

static void delayed_retry(void)
{
    HolTermStore *s = store();
    HTerm f = ht_var(s, 0, 0, -1);
    HTerm a = ht_constant(s, 1, -1), b = ht_constant(s, 2, -1), c = ht_constant(s, 3, -1);
    assert(ht_unify(s, app(s, f, a), b) == 1);
    assert(ht_pending_count(s) == 1);
    assert(ht_unify(s, f, ht_lam(s, c, -1)) == 0);
    assert(ht_pending_count(s) == 1 && ht_view(s, f).a == HT_NONE);
    assert(ht_unify(s, f, ht_lam(s, b, -1)) == 1);
    assert(ht_pending_count(s) == 0);
    assert(normal(s, app(s, f, a)).symbol == 2);
    ht_destroy(s);
    puts("PASS delayed_retry_and_atomic_failure");
}

static void wire_and_clone(void)
{
    HolTermStore *s = store();
    int64_t input[] = {2, -1, 0, 9, 0, 0, -1, 0, 2, 0, 0, -1};
    size_t offset = 0;
    HTerm term = ht_import(s, input, sizeof(input) / sizeof(*input), &offset);
    assert(term != HT_NONE && offset == sizeof(input) / sizeof(*input));
    assert(ht_view(s, ht_lookup_uid(s, 9)).uid == 9 && ht_view(s, ht_lookup_uid(s, 2)).uid == 2);
    int64_t *output = NULL;
    size_t count = 0;
    assert(ht_export(s, term, &output, &count));
    assert(count == sizeof(input) / sizeof(*input) && !memcmp(input, output, sizeof(input)));
    free(output);
    HolTermStore *copy = ht_clone(s);
    assert(copy);
    assert(ht_unify(copy, ht_lookup_uid(copy, 9), ht_nat(copy, "123")) == 1);
    assert(normal(copy, ht_lookup_uid(copy, 9)).tag == HT_NAT);
    assert(normal(s, ht_lookup_uid(s, 9)).tag == HT_VAR);
    ht_destroy(copy);
    ht_destroy(s);
    const int64_t malformed[][6] = {{9}, {0, -1, 0, 0, -1}, {4, -2, 7}, {6, 2, '1', '-'}, {3, -1}, {1, -1, -1}};
    for (size_t i = 0; i < sizeof(malformed) / sizeof(*malformed); ++i) {
        s = store();
        offset = 0;
        assert(ht_import(s, malformed[i], 6, &offset) == HT_NONE);
        assert(*ht_error(s));
        ht_destroy(s);
    }
    puts("PASS wire_validation_identity_order_and_clone");
}

static void restored_identity_and_type_flag(void)
{
    HolTermStore *s = store();
    HTCheckpoint before = ht_checkpoint(s);
    HTerm variable = ht_var(s, 1, 1, 77);
    uint64_t uid = ht_view(s, variable).uid;
    int64_t *wire;
    size_t count;
    assert(ht_export(s, variable, &wire, &count));
    assert(ht_restore(s, before));
    HolTermStore *copy = ht_clone(s);
    assert(copy);
    size_t offset = 0;
    assert(ht_import(s, wire, count, &offset) == HT_NONE);
    assert(*ht_error(s));
    offset = 0;
    HTerm restored = ht_import_restored(copy, wire, count, &offset);
    assert(restored != HT_NONE && ht_view(copy, restored).uid == uid);
    assert(ht_view(copy, restored).is_type == 1 && ht_view(copy, restored).meta == 77);
    HTerm fresh = ht_var(copy, 1, 0, -1);
    assert(ht_view(copy, fresh).uid > uid);
    assert(ht_unify(copy, restored, fresh) == 1);
    assert(normal(copy, fresh).is_type == 1);
    free(wire);
    ht_destroy(copy);
    ht_destroy(s);
    puts("PASS authorized_identity_restoration_and_type_flag");
}

static void snapshot_identity_history(void)
{
    HolTermStore *live = store();
    HTerm original = ht_var(live, 0, 0, -1);
    uint64_t original_uid = ht_view(live, original).uid;
    HolTermStore *saved = ht_clone(live);
    assert(saved);
    HTerm later = ht_var(live, 1, 1, 37);
    uint64_t later_uid = ht_view(live, later).uid;
    int64_t *wire;
    size_t count;
    assert(ht_export(live, later, &wire, &count));
    assert(ht_preserve_identity_history(saved, live));
    assert(ht_lookup_uid(saved, original_uid) == original);
    assert(ht_lookup_uid(saved, later_uid) == HT_NONE);
    assert(ht_next_uid(saved) >= ht_next_uid(live));
    HolTermStore *authorized = ht_clone(saved);
    assert(authorized);
    size_t offset = 0;
    assert(ht_import(saved, wire, count, &offset) == HT_NONE);
    assert(*ht_error(saved));
    offset = 0;
    HTerm restored = ht_import_restored(authorized, wire, count, &offset);
    assert(restored != HT_NONE && ht_view(authorized, restored).uid == later_uid);
    assert(ht_view(authorized, restored).scope == 1 && ht_view(authorized, restored).is_type == 1);
    assert(ht_view(authorized, ht_var(authorized, 0, 0, -1)).uid > later_uid);
    assert(ht_preserve_identity_history(authorized, authorized));
    free(wire);
    ht_destroy(authorized);
    ht_destroy(saved);
    ht_destroy(live);
    puts("PASS snapshot_preserves_identity_retirement");
}

static HTerm import_variable(HolTermStore *s, uint64_t uid, int restoring)
{
    assert(uid < INT64_MAX);
    int64_t wire[] = { HT_VAR, (int64_t) uid, 0, 0, -1 };
    size_t offset = 0;
    HTerm result = restoring ? ht_import_restored(s, wire, 5, &offset) : ht_import(s, wire, 5, &offset);
    assert(result == HT_NONE || offset == 5);
    return result;
}

static void expired_on_copy(HolTermStore *s, uint64_t uid)
{
    HolTermStore *copy = ht_clone(s);
    assert(copy);
    assert(import_variable(copy, uid, 0) == HT_NONE);
    assert(strstr(ht_error(copy), "expired identity"));
    ht_destroy(copy);
}

static void compact_identity_retirement(void)
{
    largest_allocation = 0;
    HolTermStore *s = store();
    HTCheckpoint empty = ht_checkpoint(s);
    for (size_t i = 0; i < 100000; ++i) {
        assert(ht_var(s, 0, 0, -1) != HT_NONE);
        assert(ht_restore(s, empty));
    }
    assert(ht_heap_count(s) == 0 && ht_next_uid(s) == 100000);
    expired_on_copy(s, 0);
    expired_on_copy(s, 50000);
    expired_on_copy(s, 99999);
    assert(largest_allocation < 4096);
    assert(import_variable(s, 50000, 1) != HT_NONE);
    allocation_testing = 1;
    failure_index = 1;
    allocation_count = 0;
    assert(ht_restore(s, empty));
    assert(allocation_count == 0);
    allocation_testing = 0;
    expired_on_copy(s, 50000);
    assert(ht_advance_uid(s, 1000000));
    assert(import_variable(s, 500000, 0) != HT_NONE);
    assert(ht_view(s, ht_var(s, 0, 0, -1)).uid == 1000000);
    ht_destroy(s);
    puts("PASS bounded_storage_for_contiguous_retirement_and_allocation_free_restore");
}

static void sparse_identity_history(void)
{
    HolTermStore *s = store();
    HTCheckpoint empty = ht_checkpoint(s);
    uint64_t sequence[] = { 10, 12, 11, 7, 6, 8, 9, 1000 };
    for (size_t i = 0; i < sizeof(sequence) / sizeof(*sequence); ++i) {
        assert(import_variable(s, sequence[i], 0) != HT_NONE);
        assert(ht_restore(s, empty));
    }
    for (uint64_t uid = 6; uid <= 12; ++uid) expired_on_copy(s, uid);
    expired_on_copy(s, 1000);
    assert(import_variable(s, 5, 0) != HT_NONE);
    assert(import_variable(s, 13, 0) != HT_NONE);
    assert(import_variable(s, 999, 0) != HT_NONE);
    HolTermStore *saved = ht_clone(s);
    assert(saved);
    HTCheckpoint checkpoint = ht_checkpoint(s);
    assert(import_variable(s, 15, 0) != HT_NONE);
    assert(ht_restore(s, checkpoint));
    assert(import_variable(s, 17, 0) != HT_NONE);
    assert(ht_advance_uid(s, 2000));
    assert(ht_preserve_identity_history(saved, s));
    assert(ht_next_uid(saved) == 2000);
    assert(ht_lookup_uid(saved, 5) != HT_NONE && ht_lookup_uid(saved, 13) != HT_NONE);
    expired_on_copy(saved, 15);
    expired_on_copy(saved, 17);
    assert(import_variable(saved, 14, 0) != HT_NONE);
    assert(import_variable(saved, 16, 0) != HT_NONE);
    assert(import_variable(saved, 1500, 0) != HT_NONE);
    assert(import_variable(saved, 17, 1) != HT_NONE);
    assert(ht_lookup_uid(s, 17) != HT_NONE);
    ht_destroy(saved);
    ht_destroy(s);
    s = store();
    empty = ht_checkpoint(s);
    assert(import_variable(s, INT64_MAX - 1, 0) != HT_NONE);
    assert(ht_next_uid(s) == INT64_MAX && ht_restore(s, empty));
    expired_on_copy(s, INT64_MAX - 1);
    assert(import_variable(s, 2, 0) != HT_NONE);
    ht_destroy(s);
    puts("PASS sparse_retirement_ranges_gaps_and_snapshot_union");
}

static void mark_roots(HTCollection *collection, void *context)
{
    for (const HTerm *root = context; *root != HT_NONE; ++root) ht_collect_mark(collection, *root);
}

static void relocate_roots(const HTCollection *collection, void *context)
{
    for (HTerm *root = context; *root != HT_NONE; ++root) *root = ht_collect_term(collection, *root);
}

/* A collection retires every identity it frees, in one pass over the ranges. */
static void collected_identity_retirement(void)
{
    static const HTCollector collector = { mark_roots, relocate_roots };
    HolTermStore *s = store();
    HTerm variables[64];
    uint64_t first = ht_next_uid(s);
    assert(ht_collect(s, 0, &collector, (HTerm[]) { HT_NONE }) == 1);
    for (size_t i = 0; i < 64; ++i) variables[i] = ht_var(s, 0, 0, -1);
    HTerm roots[] = { variables[5], variables[6], variables[20], variables[63], HT_NONE };
    assert(ht_collect(s, 0, &collector, roots) == 1 && ht_heap_count(s) == 4);
    for (uint64_t i = 0; i < 64; ++i) {
        int kept = i == 5 || i == 6 || i == 20 || i == 63;
        assert((ht_lookup_uid(s, first + i) != HT_NONE) == kept);
        if (!kept) expired_on_copy(s, first + i);
    }
    assert(ht_view(s, roots[2]).uid == first + 20);
    roots[0] = roots[1];
    roots[1] = HT_NONE;
    assert(ht_collect(s, 0, &collector, roots) == 1 && ht_heap_count(s) == 1);
    for (uint64_t i = 0; i < 64; ++i) {
        assert((ht_lookup_uid(s, first + i) != HT_NONE) == (i == 6));
        if (i != 6) expired_on_copy(s, first + i);
    }
    assert(ht_view(s, ht_var(s, 0, 0, -1)).uid == first + 64);
    assert(import_variable(s, first + 1000, 0) != HT_NONE);
    ht_destroy(s);
    puts("PASS a_collection_retires_the_identities_it_frees");
}

/* A reset gives the state between two runs: the heap and the bindings of the
    * program, and the identities, symbol marks and work limit it had. A run after
    * it numbers its variables as the run before it did. */
static void reset_between_runs(void)
{
    static const HTCollector collector = { mark_roots, relocate_roots };
    HolTermStore *s = store();
    HTerm constant = ht_constant(s, 3, -1), kept = ht_var(s, 0, 0, -1);
    size_t heap = ht_heap_count(s);
    uint64_t frontier = ht_next_uid(s);
    for (int round = 0; round < 3; ++round) {
        HTerm variables[40];
        for (size_t i = 0; i < 40; ++i) variables[i] = ht_var(s, 0, 0, -1);
        assert(ht_view(s, variables[0]).uid == frontier && ht_view(s, variables[39]).uid == frontier + 39);
        HTerm formula = ht_constant(s, 9, -1);
        assert(ht_unify(s, kept, constant) == 1 && ht_unify(s, variables[1], app(s, constant, variables[2])) == 1);
        assert(ht_mentions_arithmetic(s, formula) == 0);
        assert(ht_set_work_limit(s, 77) && ht_set_opaque_symbol(s, 9) && ht_mentions_arithmetic(s, formula) == 1);
        HTerm roots[] = { variables[7], variables[30], HT_NONE };
        assert(ht_collect(s, heap, &collector, roots) == 1 && ht_lookup_uid(s, frontier + 3) == HT_NONE);
        expired_on_copy(s, frontier + 3);
        assert(ht_reset(s, heap, frontier, 5) == 1);
        assert(ht_heap_count(s) == heap && ht_next_uid(s) == frontier && ht_work_limit(s) == 5000000);
        assert(ht_deref(s, kept) == kept && ht_view(s, kept).uid == frontier - 1 && ht_lookup_uid(s, frontier - 1) == kept);
        assert(ht_lookup_uid(s, frontier) == HT_NONE && ht_lookup_uid(s, frontier + 30) == HT_NONE && ht_pending_count(s) == 0);
    }
    assert(ht_reset(s, heap, frontier + 1, 5) == 0 && strstr(ht_error(s), "reset"));
    ht_destroy(s);
    puts("PASS a_reset_returns_to_the_state_between_two_runs");
}

/* The nodes before the first variable are sealed. A collection that keeps
    * them allocates and works in proportion to the rest of the heap, and leaves
    * every reference into them as it was. */
static void sealed_program(void)
{
    static const HTCollector collector = { mark_roots, relocate_roots };
    HolTermStore *s = store();
    HTerm constant = ht_constant(s, 3, -1), program = constant;
    for (size_t i = 0; i < 200000; ++i) program = app(s, constant, program);
    size_t kept = ht_heap_count(s);
    assert(ht_sealed(s) == 0 && ht_seal(s) == kept);
    HTerm variable = ht_var(s, 0, 0, -1);
    for (size_t i = 0; i < 100; ++i) assert(app(s, program, constant) != HT_NONE);
    HTerm value = app(s, program, constant);
    assert(ht_unify(s, variable, value) == 1 && ht_seal(s) == kept);
    HTerm roots[] = { variable, HT_NONE };
    largest_allocation = 0;
    assert(ht_collect(s, kept, &collector, roots) == 1);
    assert(largest_allocation < 16384 && ht_heap_count(s) == kept + 2 && ht_sealed(s) == kept);
    HTView bound = ht_view(s, ht_deref(s, roots[0]));
    assert(roots[0] == kept && bound.tag == HT_APP && bound.a == program && bound.b == constant);
    assert(normal(s, program).tag == HT_APP && ht_view(s, constant).symbol == 3);
    roots[0] = program;
    assert(ht_collect(s, 1, &collector, roots) == 1 && ht_sealed(s) == 1 && ht_heap_count(s) == kept && roots[0] == program);
    roots[0] = constant;
    assert(ht_collect(s, 0, &collector, roots) == 1 && ht_sealed(s) == 0 && ht_heap_count(s) == 1 && roots[0] == 0);
    ht_destroy(s);
    puts("PASS a_collection_leaves_the_sealed_program_alone");
}

static void identity_hash_deletion(void)
{
    HolTermStore *s = store();
    HTCheckpoint checkpoints[257];
    uint64_t uids[256];
    checkpoints[0] = ht_checkpoint(s);
    for (size_t i = 0; i < 256; ++i) {
        uids[i] = ((i * 137) % 256) * 64 + 9;
        assert(import_variable(s, uids[i], 0) != HT_NONE);
        checkpoints[i + 1] = ht_checkpoint(s);
    }
    for (size_t count = 256; count > 0; --count) {
        assert(ht_restore(s, checkpoints[count - 1]));
        assert(ht_lookup_uid(s, uids[count - 1]) == HT_NONE);
        for (size_t i = 0; i + 1 < count; ++i) {
            HTerm term = ht_lookup_uid(s, uids[i]);
            assert(term != HT_NONE && ht_view(s, term).uid == uids[i]);
        }
    }
    for (size_t i = 0; i < 256; ++i) expired_on_copy(s, uids[i]);
    assert(import_variable(s, 8, 0) != HT_NONE);
    assert(import_variable(s, 10, 0) != HT_NONE);
    ht_destroy(s);
    puts("PASS collision_cluster_deletion_preserves_live_identities");
}

static void unapplied_flex_dependencies(void)
{
    HolTermStore *s = store();
    HTerm x = ht_var(s, 0, 0, -1), y = ht_var(s, 1, 0, -1);
    HTerm c = ht_nominal(s, 1, -1);
    HTCheckpoint saved = ht_checkpoint(s);
    assert(ht_unify(s, app(s, x, c), y) == 1);
    assert(ht_unify(s, y, c) == 1);
    assert(normal(s, x).tag == HT_LAM && normal(s, normal(s, x).a).tag == HT_INDEX);
    assert(ht_restore(s, saved));
    assert(ht_view(s, x).a == HT_NONE && ht_view(s, y).a == HT_NONE && ht_view(s, y).scope == 1);
    HTerm f = ht_constant(s, 7, -1);
    assert(ht_unify(s, x, app(s, f, y)) == 1);
    assert(ht_view(s, y).a != HT_NONE && normal(s, y).uid != ht_view(s, y).uid);
    assert(normal(s, y).scope == 0);
    ht_destroy(s);
    puts("PASS unapplied_flex_retains_scope_dependencies_and_visible_aliases");
}

static void ground_list_sharing(void)
{
    HolTermStore *s = store();
    HTerm cons = ht_constant(s, 1, -1), nil = ht_constant(s, 2, -1);
    HTerm item = ht_constant(s, 3, -1), other = ht_constant(s, 4, -1);
    HTerm head = app(s, cons, item), different = app(s, cons, other);
    HTerm list = nil, copy = nil, mismatch = nil;
    for (size_t i = 0; i < 10000; ++i) {
        list = app(s, head, list);
        copy = app(s, head, copy);
        mismatch = app(s, i ? head : different, mismatch);
    }
    assert(ht_normalize(s, list, HT_NF) == list);
    assert(ht_unify(s, list, copy) == 1);
    assert(ht_unify(s, list, mismatch) == 0 && !*ht_error(s));
    for (HTerm tail = list; tail != nil; tail = ht_view(s, tail).b) {
        HTerm variable = ht_var(s, 0, 0, -1);
        size_t allocated = ht_heap_count(s);
        assert(ht_unify(s, variable, tail) == 1);
        assert(ht_deref(s, variable) == tail && ht_heap_count(s) == allocated);
    }
    int64_t *wire = NULL;
    size_t count = 0;
    assert(ht_export(s, list, &wire, &count));
    assert(count == 100003);
    free(wire);
    ht_destroy(s);
    puts("PASS ten_thousand_element_ground_list_sharing_equality_and_export");
}

/* A term with nominals and bound indices but no variable is stable: binding
    * it, normalizing it and substituting around it do not visit or copy it. */
static void stable_term_sharing(void)
{
    HolTermStore *s = store();
    HTerm cons = ht_constant(s, 1, -1), nil = ht_constant(s, 2, -1);
    HTerm a = ht_nominal(s, 1, -1), b = ht_nominal(s, 2, -1);
    HTerm head = app(s, cons, a), other = app(s, cons, b);
    HTerm list = nil, copy = nil, mismatch = nil;
    for (size_t i = 0; i < 10000; ++i) {
        list = app(s, head, list);
        copy = app(s, head, copy);
        mismatch = app(s, i ? head : other, mismatch);
    }
    assert(ht_unify(s, list, copy) == 1);
    assert(ht_set_work_limit(s, 64));
    assert(ht_normalize(s, list, HT_NF) == list);
    assert(ht_unify(s, list, mismatch) == 0 && !*ht_error(s));
    for (HTerm tail = list; tail != nil; tail = ht_view(s, tail).b) {
        HTerm variable = ht_var(s, 1, 0, -1);
        size_t allocated = ht_heap_count(s);
        assert(ht_unify(s, variable, tail) == 1);
        assert(ht_deref(s, variable) == tail && ht_heap_count(s) == allocated);
    }
    HTerm low = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, low, list) == 0 && !*ht_error(s) && ht_view(s, low).a == HT_NONE);
    HTerm function = ht_var(s, 1, 0, -1), fresh = ht_nominal(s, 2, -1);
    size_t allocated = ht_heap_count(s);
    assert(ht_unify(s, app(s, function, fresh), list) == 1);
    assert(ht_heap_count(s) <= allocated + 8);
    HTView constant = normal(s, function);
    assert(constant.tag == HT_LAM && ht_deref(s, constant.a) == list);
    HTerm body = app(s, app(s, cons, ht_index(s, 0)), list);
    HTView applied = normal(s, ht_apply(s, ht_lam(s, body, -1), b));
    assert(applied.tag == HT_APP && applied.b == list);
    HTerm inside = ht_var(s, 2, 0, -1);
    HTerm holder = app(s, app(s, cons, inside), list);
    assert(ht_unify(s, inside, a) == 1);
    HTerm settled = ht_var(s, 2, 0, -1);
    allocated = ht_heap_count(s);
    assert(ht_unify(s, settled, holder) == 1);
    assert(ht_deref(s, settled) != holder && ht_heap_count(s) == allocated + 2);
    HTerm again = ht_var(s, 2, 0, -1);
    allocated = ht_heap_count(s);
    assert(ht_unify(s, again, settled) == 1);
    assert(ht_deref(s, again) == ht_deref(s, settled) && ht_heap_count(s) == allocated);
    assert(!*ht_error(s));
    ht_destroy(s);
    puts("PASS ten_thousand_element_stable_list_binding_scope_and_substitution");
}

/* Whether an abstraction is an eta-redex is known from its summary, also when
    * the bound variable occurs only below another binder. */
static void stable_eta_summary(void)
{
    HolTermStore *s = store();
    HTerm g = ht_constant(s, 7, -1), h = ht_constant(s, 8, -1);
    HTerm inner = ht_lam(s, app(s, app(s, g, ht_index(s, 0)), ht_index(s, 1)), -1);
    HTerm used = ht_lam(s, app(s, app(s, h, inner), ht_index(s, 0)), -1);
    HTerm variable = ht_var(s, 0, 0, -1);
    size_t allocated = ht_heap_count(s);
    assert(ht_unify(s, variable, used) == 1);
    assert(ht_deref(s, variable) == used && ht_heap_count(s) == allocated);
    HTerm outer = ht_lam(s, app(s, app(s, g, ht_index(s, 0)), ht_index(s, 2)), -1);
    HTerm redex = ht_lam(s, ht_lam(s, app(s, app(s, h, outer), ht_index(s, 0)), -1), -1);
    HTerm reduced = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, reduced, redex) == 1);
    HTView abstraction = normal(s, reduced);
    assert(abstraction.tag == HT_LAM);
    HTView application = normal(s, abstraction.a);
    assert(application.tag == HT_APP && normal(s, application.a).symbol == 8);
    HTView kept = normal(s, application.b);
    assert(kept.tag == HT_LAM && normal(s, normal(s, kept.a).b).a == 1);
    HTerm twice = ht_lam(s, app(s, app(s, g, ht_index(s, 0)), ht_index(s, 0)), -1);
    HTerm same = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, same, twice) == 1 && ht_deref(s, same) == twice);
    HTerm expanded = ht_lam(s, app(s, g, ht_index(s, 0)), -1);
    assert(ht_unify(s, expanded, g) == 1);
    assert(!*ht_error(s));
    ht_destroy(s);
    puts("PASS eta_redexes_are_known_from_the_summary_of_a_stable_term");
}

/* The depth of a term is bounded by memory, not by the C stack: a chain of
    * 200,000 applications is substituted into, abstracted, normalized through
    * its variable links, searched and compared. */
static void deep_terms(void)
{
    enum { DEPTH = 200000 };
    HolTermStore *s = store();
    HTerm f = ht_constant(s, 7, -1), a = ht_nominal(s, 1, -1), b = ht_nominal(s, 1, -1);
    HTerm open = ht_index(s, 0), over_a = a, linked = ht_var(s, 1, 0, -1), hole = linked;
    for (size_t i = 0; i < DEPTH; ++i) {
        open = app(s, f, open);
        over_a = app(s, f, over_a);
    }
    HTerm lambda = ht_lam(s, open, -1);
    HTerm applied = ht_normalize(s, app(s, lambda, a), HT_NF);
    assert(applied != HT_NONE && ht_unify(s, applied, over_a) == 1);
    HTerm function = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, app(s, function, a), over_a) == 1);
    assert(ht_unify(s, function, lambda) == 1);
    HTerm over_b = ht_normalize(s, app(s, function, b), HT_NF);
    assert(over_b != HT_NONE && ht_unify(s, over_b, over_a) == 0 && !*ht_error(s));
    for (size_t i = 0; i < DEPTH; ++i) {
        HTerm tail = ht_var(s, 1, 0, -1);
        assert(ht_unify(s, hole, app(s, f, tail)) == 1);
        hole = tail;
    }
    HTerm occurring = ht_var(s, 1, 0, -1);
    HTCheckpoint before = ht_checkpoint(s);
    assert(ht_unify(s, hole, occurring) == 1);
    assert(ht_unify(s, occurring, linked) == 0 && !*ht_error(s));
    assert(ht_restore(s, before));
    assert(ht_unify(s, linked, over_a) == 1 && ht_deref(s, hole) == a);
    assert(ht_normalize(s, linked, HT_NF) != HT_NONE);
    HTerm expanded = ht_lam(s, app(s, app(s, f, over_a), ht_index(s, 0)), -1);
    HTerm reduced = ht_var(s, 1, 0, -1);
    assert(ht_unify(s, reduced, expanded) == 1 && normal(s, reduced).tag == HT_APP);
    int64_t *wire = NULL;
    size_t count = 0;
    assert(ht_export(s, linked, &wire, &count) && count == 5 * (size_t) DEPTH + 4);
    free(wire);
    assert(!*ht_error(s));
    ht_destroy(s);
    puts("PASS two_hundred_thousand_deep_terms_do_not_use_the_c_stack");
}

/* A wire is written and read, and two rigid terms are unified, however deep
    * the terms are on the function side and in an argument that is not the last:
    * a pair nested 200000 times in its first component, and a constant applied
    * to 200000 arguments. */
static void deep_function_sides(void)
{
    enum { DEPTH = 200000 };
    HolTermStore *s = store();
    assert(ht_set_work_limit(s, 100000000));
    HTerm pair = ht_constant(s, 5, -1), a = ht_constant(s, 6, -1), b = ht_constant(s, 7, -1);
    HTerm hole = ht_var(s, 0, 0, -1), first = ht_var(s, 0, 0, -1);
    HTerm open = hole, closed = a, wide = app(s, pair, first), full = app(s, pair, b);
    for (size_t i = 0; i < DEPTH; ++i) {
        open = app(s, app(s, pair, open), b);
        closed = app(s, app(s, pair, closed), b);
        wide = app(s, wide, a);
        full = app(s, full, a);
    }
    int64_t *wire = NULL, *again = NULL;
    size_t count = 0, repeated = 0, offset = 0;
    assert(ht_export(s, closed, &wire, &count) && count == 10 * (size_t) DEPTH + 3);
    HTerm read = ht_import(s, wire, count, &offset);
    assert(read != HT_NONE && offset == count && read != closed);
    assert(ht_export(s, read, &again, &repeated) && repeated == count && !memcmp(wire, again, count * sizeof(*wire)));
    free(wire);
    free(again);
    assert(ht_unify(s, open, read) == 1 && ht_view(s, ht_deref(s, hole)).tag == HT_CONST && ht_view(s, ht_deref(s, hole)).symbol == 6);
    assert(ht_unify(s, wide, full) == 1 && ht_deref(s, first) == b);
    assert(ht_export(s, wide, &wire, &count) && count == 5 * (size_t) DEPTH + 8);
    offset = 0;
    read = ht_import(s, wire, count, &offset);
    assert(read != HT_NONE && offset == count && ht_unify(s, read, full) == 1);
    free(wire);
    HTerm other = app(s, app(s, pair, closed), a);
    assert(ht_unify(s, other, app(s, app(s, pair, open), b)) == 0 && !*ht_error(s));
    ht_destroy(s);
    puts("PASS wires_and_rigid_terms_are_deep_on_the_function_side");
}

static void arithmetic_mentions(void)
{
    HolTermStore *s = store();
    HTerm plus = ht_constant(s, 5, -1), f = ht_constant(s, 7, -1);
    HTerm a = ht_nominal(s, 1, -1), two = ht_nat(s, "2");
    HTerm sum = app(s, app(s, plus, a), two);
    HTerm variable = ht_var(s, 1, 0, -1);
    HTerm holder = ht_lam(s, app(s, app(s, f, variable), ht_index(s, 0)), -1);
    assert(ht_mentions_arithmetic(s, sum) == 0 && ht_mentions_arithmetic(s, holder) == 0);
    assert(ht_set_arithmetic_symbol(s, 5));
    assert(ht_mentions_arithmetic(s, sum) == 1 && ht_mentions_arithmetic(s, holder) == 0);
    assert(ht_mentions_arithmetic(s, two) == 0 && ht_mentions_arithmetic(s, app(s, f, two)) == 0);
    HTCheckpoint before = ht_checkpoint(s);
    assert(ht_unify(s, variable, sum) == 1);
    assert(ht_mentions_arithmetic(s, holder) == 1);
    assert(ht_restore(s, before));
    assert(ht_mentions_arithmetic(s, holder) == 0);
    assert(ht_mentions_arithmetic(s, app(s, ht_constant(s, 0, -1), variable)) == 1);
    assert(ht_mentions_arithmetic(s, app(s, ht_constant(s, 0, -1), two)) == 0);
    HTerm formula = app(s, ht_constant(s, 9, -1), a);
    assert(ht_mentions_arithmetic(s, formula) == 0);
    assert(ht_set_opaque_symbol(s, 9));
    assert(ht_mentions_arithmetic(s, formula) == 1);
    assert(!ht_set_arithmetic_symbol(s, SIZE_MAX) && strstr(ht_error(s), "arithmetic"));
    ht_destroy(s);
    puts("PASS arithmetic_mentions_follow_marks_bindings_and_rollback");
}

static void ground_cache_invalidation(void)
{
    HolTermStore *s = store();
    HTerm f = ht_constant(s, 7, -1), one = ht_nat(s, "1");
    HTerm value = app(s, f, one);
    assert(ht_normalize(s, value, HT_NF) == value);
    ht_set_successor(s, 7);
    HTView reduced = normal(s, value);
    assert(reduced.tag == HT_NAT && !strcmp(reduced.digits, "2"));
    HTerm opaque = ht_constant(s, 9, -1);
    HTerm formula = app(s, opaque, one);
    HTerm variable = ht_var(s, 0, 0, -1);
    assert(ht_set_opaque_symbol(s, 9));
    assert(ht_unify(s, variable, formula) == 0);
    ht_destroy(s);

    s = store();
    f = ht_constant(s, 7, -1);
    variable = ht_var(s, 0, 0, -1);
    value = app(s, f, variable);
    HTCheckpoint before = ht_checkpoint(s);
    assert(ht_unify(s, variable, ht_nat(s, "1")) == 1);
    reduced = normal(s, value);
    assert(!strcmp(normal(s, reduced.b).digits, "1"));
    assert(ht_restore(s, before));
    assert(ht_unify(s, variable, ht_nat(s, "2")) == 1);
    reduced = normal(s, value);
    assert(!strcmp(normal(s, reduced.b).digits, "2"));
    ht_destroy(s);
    puts("PASS ground_cache_respects_configuration_and_variable_rollback");
}

static void opaque_formula(void)
{
    HolTermStore *s = store();
    assert(ht_set_opaque_symbol(s, 9));
    HTerm formula = ht_constant(s, 9, -1);
    HTerm x = ht_var(s, 0, 0, -1), y = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, x, formula) == 0);
    assert(ht_unify(s, formula, formula) == 1);
    assert(ht_unify(s, app(s, formula, x), app(s, formula, y)) == 1);
    assert(ht_pending_count(s) == 1);
    assert(ht_unify(s, x, y) == 1);
    assert(ht_pending_count(s) == 0);
    HolTermStore *copy = ht_clone(s);
    assert(copy);
    HTerm fresh = ht_var(copy, 0, 0, -1);
    assert(ht_unify(copy, fresh, formula) == 0);
    ht_destroy(copy);
    ht_destroy(s);
    puts("PASS opaque_formula_binding_identity_and_delay");
}

static void checked_assignment(void)
{
    HolTermStore *s = store();
    assert(ht_set_opaque_symbol(s, 9));
    HTerm formula = ht_constant(s, 9, -1);
    HTerm x = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, x, formula) == 0);
    assert(ht_assign_checked(s, x, formula) == 1);
    assert(normal(s, x).tag == HT_CONST && normal(s, x).symbol == 9);
    HTerm low = ht_var(s, 0, 0, -1);
    HTerm high = ht_var(s, 1, 0, -1);
    HTerm nominal = ht_nominal(s, 1, -1);
    assert(ht_assign_checked(s, low, high) == 0);
    assert(ht_assign_checked(s, low, nominal) == 0);
    assert(ht_assign_checked(s, low, ht_index(s, 0)) == 0);
    assert(ht_assign_checked(s, low, app(s, formula, low)) == 0);
    assert(ht_view(s, low).a == HT_NONE && ht_view(s, high).scope == 1);
    HTerm f = ht_var(s, 0, 0, -1);
    HTerm a = ht_constant(s, 2, -1), b = ht_constant(s, 3, -1);
    assert(ht_unify(s, app(s, f, a), b) == 1 && ht_pending_count(s) == 1);
    assert(ht_assign_checked(s, f, ht_lam(s, a, -1)) == 0);
    assert(ht_view(s, f).a == HT_NONE && ht_pending_count(s) == 1);
    assert(ht_assign_checked(s, f, ht_lam(s, b, -1)) == 1 && ht_pending_count(s) == 0);
    assert(ht_assign_checked(s, f, ht_lam(s, a, -1)) == 0);
    ht_destroy(s);
    puts("PASS checked_assignment_opaque_scope_occurs_and_atomic_retry");
}

static HTerm duplication_term(HolTermStore *s, unsigned count)
{
    HTerm parameter = ht_index(s, 0);
    HTerm pair = ht_constant(s, 1, -1);
    HTerm duplicate = ht_lam(s, app(s, app(s, pair, parameter), parameter), -1);
    HTerm term = ht_constant(s, 2, -1);
    while (count--) {
        term = app(s, duplicate, term);
    }
    return term;
}

static void primitive_work_limit(void)
{
    HolTermStore *s = store();
    assert(ht_work_limit(s) == UINT64_C(5000000));
    assert(ht_set_work_limit(s, 5000));
    HTerm variable = ht_var(s, 0, 0, -1);
    HTerm large = duplication_term(s, 20);
    assert(ht_unify(s, variable, large) == -1);
    assert(strstr(ht_error(s), "work limit"));
    assert(ht_view(s, variable).a == HT_NONE);
    ht_destroy(s);
    s = store();
    assert(ht_set_work_limit(s, 1000000));
    HTerm small = duplication_term(s, 6);
    variable = ht_var(s, 0, 0, -1);
    assert(ht_unify(s, variable, small) == 1);
    HolTermStore *copy = ht_clone(s);
    assert(copy && ht_work_limit(copy) == 1000000);
    ht_destroy(copy);
    assert(ht_set_work_limit(s, 1));
    int64_t *wire = NULL;
    size_t count = 0;
    assert(!ht_export(s, variable, &wire, &count));
    assert(strstr(ht_error(s), "work limit") && !wire && !count);
    ht_destroy(s);
    s = store();
    assert(!ht_set_work_limit(s, 0));
    assert(strstr(ht_error(s), "positive"));
    ht_destroy(s);
    puts("PASS bounded_nested_primitive_work_and_configuration");
}

static void normalization_limit(void)
{
    HolTermStore *s = store();
    HTerm index = ht_index(s, 0);
    HTerm self = ht_lam(s, app(s, index, index), -1);
    assert(ht_normalize(s, app(s, self, self), HT_NF) == HT_NONE);
    assert(*ht_error(s));
    ht_destroy(s);
    puts("PASS nonterminating_raw_term_is_controlled");
}

static int allocation_scenario(void)
{
    HolTermStore *s = ht_create();
    if (!s) {
        return 0;
    }
    ht_set_successor(s, 0);
    if (!ht_set_opaque_symbol(s, 9)) {
        ht_destroy(s);
        return 0;
    }
    HTerm f = ht_var(s, 0, 0, -1);
    HTerm g = ht_var(s, 0, 0, -1);
    HTerm c = ht_nominal(s, 1, 17);
    HTerm lhs = ht_app(s, f, c, -1);
    HTerm rhs = ht_app(s, ht_app(s, g, c, -1), c, -1);
    int okay = lhs != HT_NONE && rhs != HT_NONE && ht_unify(s, lhs, rhs) == 1;
    if (okay) {
        HTCheckpoint before = ht_checkpoint(s);
        for (size_t i = 0; okay && i < 40; ++i) {
            okay = ht_var(s, 0, 0, -1) != HT_NONE;
        }
        if (okay) okay = ht_restore(s, before);
    }
    if (okay) {
        HolTermStore *copy = ht_clone(s);
        okay = copy != NULL;
        for (size_t i = 0; okay && i < 40; ++i) {
            okay = ht_var(s, 0, 0, -1) != HT_NONE;
        }
        if (okay) {
            okay = ht_preserve_identity_history(copy, s);
        }
        ht_destroy(copy);
    }
    int64_t *wire = NULL;
    size_t count = 0;
    if (okay) {
        okay = ht_export(s, f, &wire, &count);
    }
    free(wire);
    if (okay) {
        HTerm value = ht_nat(s, "99999999999999999999999999999999");
        HTerm successor = ht_constant(s, 0, -1);
        okay = value != HT_NONE && successor != HT_NONE && ht_app(s, successor, value, -1) != HT_NONE;
    }
    ht_destroy(s);
    return okay;
}

static void allocation_failures(void)
{
    allocation_testing = 1;
    allocation_count = 0;
    failure_index = SIZE_MAX;
    assert(allocation_scenario());
    size_t total = allocation_count;
    for (size_t i = 1; i <= total; ++i) {
        allocation_count = 0;
        failure_index = i;
        assert(!allocation_scenario());
    }
    allocation_testing = 0;
    printf("PASS allocation failure cleanup (%zu paths)\n", total);
}

int main(void)
{
    beta_capture();
    naturals();
    scope_and_rollback();
    lambda_pruning();
    same_head_pruning();
    delayed_retry();
    wire_and_clone();
    normalization_limit();
    opaque_formula();
    checked_assignment();
    primitive_work_limit();
    restored_identity_and_type_flag();
    snapshot_identity_history();
    compact_identity_retirement();
    sparse_identity_history();
    identity_hash_deletion();
    collected_identity_retirement();
    reset_between_runs();
    sealed_program();
    unapplied_flex_dependencies();
    ground_list_sharing();
    stable_term_sharing();
    stable_eta_summary();
    deep_terms();
    deep_function_sides();
    arithmetic_mentions();
    ground_cache_invalidation();
    allocation_failures();
    return 0;
}

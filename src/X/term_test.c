#include "term.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static size_t failure_index, allocation_count;
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
    return allocation_fails() ? NULL : __real_malloc(count);
}

void *__wrap_calloc(size_t count, size_t width)
{
    return allocation_fails() ? NULL : __real_calloc(count, width);
}

void *__wrap_realloc(void *old, size_t count)
{
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
    allocation_failures();
    return 0;
}

#include "term.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static int64_t number(void)
{
    int64_t value;
    if (scanf("%" SCNd64, &value) != 1) {
        fputs("bad comparison input\n", stderr);
        exit(2);
    }
    return value;
}

static HTerm read_term(HolTermStore *store)
{
    size_t count = (size_t) number();
    int64_t *words = malloc(count * sizeof(*words));
    if (!words) {
        exit(2);
    }
    for (size_t i = 0; i < count; ++i) {
        words[i] = number();
    }
    size_t offset = 0;
    HTerm term = ht_import(store, words, count, &offset);
    free(words);
    if (term == HT_NONE || offset != count) {
        fprintf(stderr, "import: %s\n", ht_error(store));
        exit(2);
    }
    return term;
}

static void print_term(HolTermStore *store, HTerm term)
{
    int64_t *words;
    size_t count;
    if (!ht_export(store, term, &words, &count)) {
        fprintf(stderr, "export: %s\n", ht_error(store));
        exit(2);
    }
    printf(",%zu", count);
    for (size_t i = 0; i < count; ++i) {
        printf(",%" PRId64, words[i]);
    }
    free(words);
}

int main(void)
{
    HolTermStore *store = ht_create();
    if (!store) {
        return 2;
    }
    ht_set_successor(store, 0);
    size_t variables = (size_t) number();
    HTerm *roots = malloc((variables ? variables : 1) * sizeof(*roots));
    if (!roots) {
        return 2;
    }
    for (size_t i = 0; i < variables; ++i) {
        roots[i] = read_term(store);
    }
    size_t constants = (size_t) number();
    for (size_t i = 0; i < constants; ++i) {
        (void) read_term(store);
    }
    ht_advance_uid(store, 100);
    size_t equations = (size_t) number();
    int status = 1;
    for (size_t i = 0; i < equations; ++i) {
        HTerm left = read_term(store);
        HTerm right = read_term(store);
        if (status == 1) {
            status = ht_unify(store, left, right);
        }
    }
    if (status != 1) {
        printf("[%d]\n", status);
        if (status < 0) {
            fprintf(stderr, "%s\n", ht_error(store));
        }
    } else {
        printf("[1,%zu", variables);
        for (size_t i = 0; i < variables; ++i) {
            print_term(store, roots[i]);
        }
        size_t pending = ht_pending_count(store);
        printf(",%zu", pending);
        for (size_t i = 0; i < pending; ++i) {
            HTerm left, right;
            ht_pending(store, i, &left, &right);
            print_term(store, left);
            print_term(store, right);
        }
        puts("]");
    }
    free(roots);
    ht_destroy(store);
    return 0;
}

#ifndef HOL_V1_MACHINE_H
#define HOL_V1_MACHINE_H

#include <stddef.h>
#include <stdint.h>

typedef struct HolV1Machine HolV1Machine;

/* Wordcode: header[8] = magic, version, terms, instructions, clauses,
    * query slots, query entry, symbols. This is followed by term[3],
    * instruction[4], and clause[4] records. Term application children precede
    * their parent. Reserved operands are zero. Calls on one machine must be
    * serialized; separate machines are independent. */
/* This API accepts version 1 only; version 2 uses higher_machine.h directly.
    * The machine owns a decoded copy. A non-NULL result may carry a validation
    * error, reported by next/error. NULL means allocation failed. */
HolV1Machine *hol_v1_create(const int64_t *code, size_t length);
/* 1: answer, 0: exhausted, -1: error, 2: instruction-budget yield.
    * On 2 the caller may service cancellation and call next again. */
int hol_v1_next(HolV1Machine *machine);
/* An answer contains every query slot, in order, in prefix form:
    * 0, variable heap ID; 1, symbol ID; or 2, function subtree, argument subtree.
    * Initial query variables have heap IDs 0 through query slots - 1. */
size_t hol_v1_answer_size(const HolV1Machine *machine);
int hol_v1_answer(HolV1Machine *machine, int64_t *output, size_t capacity);
const char *hol_v1_error(const HolV1Machine *machine);
void hol_v1_destroy(HolV1Machine *machine);

#endif

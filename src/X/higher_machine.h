#ifndef HOL_V2_MACHINE_H
#define HOL_V2_MACHINE_H

#include <stddef.h>
#include <stdint.h>

typedef struct HolV2Machine HolV2Machine;

/* V2 wordcode header[8]: magic=0x484f4c31, version=2, term count,
    * symbol count, fact count, query-slot count, query term root, metadata count.
    * Sections follow in this order:
    *   query slots[2]: is_type, metadata (-1 means absent)
    *   symbols[1]: role (enum HolV2Role)
    *   templates[6]: tag,a,b,c,d,metadata; unused operands are zero
    *   facts[2]: predicate symbol (-1 means inspect dynamically), template root
    *   remaining words: decimal ASCII payload, addressed relative to its start.
    * Template tags: 0=query VAR(a=slot), 1=CONST(a=symbol), 2=APP(a=fn,b=arg),
    * 3=INDEX(a=index), 4=LAM(a=body), 5=NAT(a=payload offset,b=length), 6=WILD.
    * Child templates precede their parents. Every goal executes as native EXEC
    * over its compiled term graph; clauses retain their quantifier/lambda nodes.
    */
enum HolV2Role {
    HV2_ORDINARY, HV2_TY_PI, HV2_IF, HV2_TRUE, HV2_FAIL, HV2_CUT,
    HV2_AND, HV2_OR, HV2_IMPLY, HV2_PI, HV2_SIGMA, HV2_DEBUG,
    HV2_IS, HV2_EQ, HV2_LE, HV2_LT, HV2_GE, HV2_GT,
    HV2_READ, HV2_PRINT, HV2_PRESBURGER, HV2_SUCCESSOR
};

enum HolV2Event {
    HV2_EVENT_PRIMITIVE = 1,
    HV2_EVENT_SETTLE = 2,
    HV2_EVENT_IMPLY = 3,
    HV2_EVENT_DEBUG = 4,
    HV2_EVENT_EQUALITY = 5
};

HolV2Machine *hol_v2_create(const int64_t *code, size_t length);
void hol_v2_destroy(HolV2Machine *machine);
const char *hol_v2_error(const HolV2Machine *machine);
/* -1 error, 0 exhausted, 1 answer, 2 cancellation yield, 3 host service.
    * Clause trials and failed-choice traversal share the scheduler budget;
    * a yielded search can be cloned/restored before the next call. */
int hol_v2_next(HolV2Machine *machine);

/* Buffers are owned by the machine until its next mutating API call.
    * Call size then copy. Copy returns -1 on invalid capacity, otherwise 1.
    * Query answer: [query-count, term-wire...]. All term-wire uses term.h tags.
    * State: [variable-count, raw-VAR-wire, dereferenced-value-wire, ...,
    *         disagreement-count, lhs-wire, rhs-wire, ...].
    * Event terms: [root-count, term-wire...]; one goal/antecedent root normally,
    * zero roots for SETTLE. Event info[6] is kind, host-state-token,
    * premise-token, scope, call-id, auxiliary. SETTLE auxiliary=1 at answer.
    */
size_t hol_v2_answer_size(HolV2Machine *machine);
int hol_v2_answer(HolV2Machine *machine, int64_t *output, size_t capacity);
size_t hol_v2_state_size(HolV2Machine *machine);
int hol_v2_state(HolV2Machine *machine, int64_t *output, size_t capacity);
size_t hol_v2_event_size(HolV2Machine *machine);
int hol_v2_event(HolV2Machine *machine, int64_t *output, size_t capacity);
int hol_v2_event_info(const HolV2Machine *machine, int64_t *output, size_t capacity);
uint64_t hol_v2_host_state(const HolV2Machine *machine);

size_t hol_v2_frames_size(HolV2Machine *machine);
int hol_v2_frames(HolV2Machine *machine, int64_t *output, size_t capacity);
/* Compact metadata from pending frames: [count, raw VAR/NOMINAL wires...].
    * Preserves all occurrences in frame traversal order: repeated type-binder
    * declarations can affect the metadata of later variables and nominals. */
size_t hol_v2_declarations_size(HolV2Machine *machine);
int hol_v2_declarations(HolV2Machine *machine, int64_t *output, size_t capacity);

/* Bindings: [count, lhs-term-wire, rhs-term-wire, ...]. result=0 rejects this branch;
    * 1 continues. For EQUALITY use 2=true, 3=false, 4=unknown (after definitions);
    * matching local hypotheses take precedence over that result.
    * IMPLY returns a lexical premise token; other events retain the old token.
    * host state tokens are immutable host-owned values saved in choice points.
    * Equality responses schedule clause search; search errors are reported by next.
    */
int hol_v2_resume(HolV2Machine *machine, int result, uint64_t host_state,
    uint64_t premises, const int64_t *bindings, size_t length);
int hol_v2_assign(HolV2Machine *machine, const int64_t *bindings, size_t length);
void hol_v2_set_debugging(HolV2Machine *machine, int enabled);
int hol_v2_ensure_symbol(HolV2Machine *machine, size_t symbol, int role);
uint64_t hol_v2_reserve_uid(HolV2Machine *machine);
/* Positive node-visit budget for one atomic term operation; default 5000000.
    * Exhaustion is an execution/resource error, never logical failure. Nested
    * normalization/unification calls share a budget. Restore keeps the live
    * setting, so raising a limit is not undone by restoring a proof snapshot. */
int hol_v2_set_work_limit(HolV2Machine *machine, uint64_t visits);
uint64_t hol_v2_work_limit(const HolV2Machine *machine);

/* Snapshots own a deep copy. Restoring preserves the live monotonic UID/call
    * counters, so identities created after a snapshot can never be reused. */
HolV2Machine *hol_v2_clone(const HolV2Machine *machine);
int hol_v2_restore(HolV2Machine *machine, const HolV2Machine *snapshot);

#endif

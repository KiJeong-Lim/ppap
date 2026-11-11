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
    HV2_READ, HV2_PRINT, HV2_PRESBURGER, HV2_SUCCESSOR, HV2_FLEX,
    HV2_ARITHMETIC, HV2_NATURAL
};
/* HV2_FLEX is decided by the machine itself: `flex T` succeeds exactly when the
    * head of T, below its leading abstractions and after dereferencing, is an
    * unbound variable. It binds nothing and raises no host event.
    * HV2_ARITHMETIC marks a function that the host evaluates (+, -, *, /) and
    * HV2_NATURAL the type of naturals. They are ordinary constants to the search.
    * An equality whose type is not HV2_NATURAL and whose sides, as bound now,
    * contain no HV2_ARITHMETIC, HV2_SUCCESSOR or HV2_PRESBURGER symbol raises no
    * host event: the host would answer "unknown" (4) without reading a state.
    * An implication whose antecedent is a conjunction of atoms and clauses with
    * ordinary heads raises none either: the host would add no premise. */

enum HolV2Event {
    HV2_EVENT_PRIMITIVE = 1,
    HV2_EVENT_SETTLE = 2,
    HV2_EVENT_IMPLY = 3,
    HV2_EVENT_DEBUG = 4,
    HV2_EVENT_EQUALITY = 5
};

HolV2Machine *hol_v2_create(const int64_t *code, size_t length);
/* A machine keeps its program across runs. A fragment is wordcode whose symbol
    * count is the total after it and whose symbol section lists the roles of the
    * symbols the machine does not have yet; its templates, clauses and digits
    * are its own, numbered from zero.
    *   extend: no query slot, query root -1. Its symbols and clauses join the
    *     program, after the ones already there.
    *   query: no clause. Its symbols and its query last for one run.
    *   idle: leaves the run and releases what it allocated.
    * extend and query leave the current run first. After leaving a run the
    * machine numbers variables, calls and host states as the created machine
    * did, and no snapshot of that run can be restored. 1, or -1 with the
    * machine in error. */
int hol_v2_extend(HolV2Machine *machine, const int64_t *code, size_t length);
int hol_v2_query(HolV2Machine *machine, const int64_t *code, size_t length);
int hol_v2_idle(HolV2Machine *machine);
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
/* Root state: the State layout restricted to the query slots (with_query) or
    * to no variable at all, followed by every disagreement. Copy it with
    * hol_v2_state. It suffices while the host holds no constraint or premise. */
size_t hol_v2_root_state_size(HolV2Machine *machine, int with_query);
size_t hol_v2_pending_count(const HolV2Machine *machine);
/* Every identity created so far is below this bound. */
uint64_t hol_v2_uid_frontier(const HolV2Machine *machine);
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

/* Unreachable terms, continuations and hypotheses are compacted between two
    * goals once the term heap has grown by its own size since the previous
    * collection, and by at least this many nodes (default 65536; 0 collects
    * before every goal). Identities exported to the host are kept. */
void hol_v2_set_collection_step(HolV2Machine *machine, size_t nodes);
size_t hol_v2_heap_count(const HolV2Machine *machine);
size_t hol_v2_collections(const HolV2Machine *machine);

/* Snapshots own a deep copy. Restoring preserves the live monotonic UID/call
    * counters, so identities created after a snapshot can never be reused. */
HolV2Machine *hol_v2_clone(const HolV2Machine *machine);
int hol_v2_restore(HolV2Machine *machine, const HolV2Machine *snapshot);

#endif

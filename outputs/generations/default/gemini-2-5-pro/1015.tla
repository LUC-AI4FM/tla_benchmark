---- MODULE VoucherLifeCycle ----
EXTENDS TLC, FiniteSets

CONSTANT Vouchers

VARIABLE voucher_state

\* The set of possible states for a voucher according to its life-cycle.
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

\* TypeOK is the main type-correctness invariant for the specification.
\* It asserts that `voucher_state` is a well-formed function mapping every
\* voucher to one of the allowed states. This single property captures both
\* "type correctness" (the variable has the structure of a function from
\* Vouchers to VoucherStates) and the "consistency invariant" (each voucher's
\* state is a valid state in the life-cycle machine).
TypeOK == voucher_state \in [Vouchers -> VoucherStates]

\* The initial state predicate. All vouchers begin in the "phantom" state.
Init == voucher_state = [v \in Vouchers |-> "phantom"]

\* A voucher `v` is issued, transitioning from "phantom" to "valid".
Issue(v) ==
    /\ voucher_state[v] = "phantom"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "valid"]

\* A valid voucher `v` is redeemed, entering a terminal "redeemed" state.
Redeem(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "redeemed"]

\* A valid voucher `v` is cancelled, entering a terminal "cancelled" state.
Cancel(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "cancelled"]

\* A valid voucher `v` is transferred. This is a stuttering action
\* that does not change the voucher's state.
Transfer(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = voucher_state

\* The next-state relation for the system. In any step, some voucher `v`
\* can transition according to one of the allowed actions.
Next ==
    \E v \in Vouchers :
        \/ Issue(v)
        \/ Redeem(v)
        \/ Cancel(v)
        \/ Transfer(v)

\* The complete temporal specification. The system starts in a state satisfying
\* Init and every subsequent step is either a Next step or a stuttering step
\* (where voucher_state remains unchanged).
Spec == Init /\ [][Next]_<<voucher_state>>

\* This theorem states that the TypeOK invariant holds in every reachable state
\* of any behavior satisfying the specification Spec. This corresponds to the
\* requirement that "the conjunction of type correctness and consistency is
\* always preserved".
THEOREM Spec => []TypeOK

=============================================================================
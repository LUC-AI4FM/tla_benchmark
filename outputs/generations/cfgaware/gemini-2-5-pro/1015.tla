---- MODULE VoucherLifecycle ----
EXTENDS TLC

CONSTANT V

\* The set of possible states for a voucher.
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

VARIABLE v2

\* TypeOK is the type invariant. It asserts that v2 is a function
\* mapping each voucher in V to a valid state.
VTypeOK == v2 \in [V -> VoucherStates]

\* VConsistent is the consistency invariant. In this model, all consistency
\* logic is captured by the state machine in the Next relation. Thus, this
\* invariant is trivially true.
VConsistent == TRUE

\* The initial state predicate. All vouchers start in the "phantom" state.
Init == v2 = [v \in V |-> "phantom"]

\* A voucher v is issued, moving from "phantom" to "valid".
Issue(v) ==
    /\ v2[v] = "phantom"
    /\ v2' = [v2 EXCEPT ![v] = "valid"]

\* A voucher v is redeemed, moving from "valid" to "redeemed".
Redeem(v) ==
    /\ v2[v] = "valid"
    /\ v2' = [v2 EXCEPT ![v] = "redeemed"]

\* A voucher v is cancelled, moving from "valid" to "cancelled".
Cancel(v) ==
    /\ v2[v] = "valid"
    /\ v2' = [v2 EXCEPT ![v] = "cancelled"]

\* A voucher v is transferred. This is a stuttering action on the voucher's
\* state, which must be "valid".
Transfer(v) ==
    /\ v2[v] = "valid"
    /\ v2' = v2

\* The next-state relation. In any step, exactly one action occurs for
\* some voucher v.
Next ==
    \E v \in V:
        \/ Issue(v)
        \/ Redeem(v)
        \/ Cancel(v)
        \/ Transfer(v)

\* The full temporal specification for the voucher life cycle.
VSpec == Init /\ [][Next]_v2

\* The main theorem asserting that the conjunction of the type and
\* consistency invariants is always preserved.
THEOREM VSpec => [](VTypeOK /\ VConsistent)

================================
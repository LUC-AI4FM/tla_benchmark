---------------------------- MODULE VoucherLifeCycle ----------------------------
\* A TLA+ specification modeling the life cycle of vouchers based on RFC 3506
\* with decoupled tuple components

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    VoucherIds,      \* Set of all possible voucher identifiers
    MaxVouchers      \* Maximum number of vouchers to consider

VARIABLES
    voucherState,    \* Function mapping voucher id to its current state
    lifecycleState,  \* Function mapping voucher id to lifecycle machine state
    issuedVouchers   \* Set of vouchers that have been issued

\* Voucher states as constants
Phantom == "phantom"
Valid == "valid"
Redeemed == "redeemed"
Cancelled == "cancelled"

\* Set of all possible voucher states
VoucherStates == {Phantom, Valid, Redeemed, Cancelled}

\* Lifecycle machine states (decoupled from voucher states)
LifecycleStates == {"pre_issue", "active", "terminal"}

vars == <<voucherState, lifecycleState, issuedVouchers>>

-----------------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ voucherState \in [VoucherIds -> VoucherStates]
    /\ lifecycleState \in [VoucherIds -> LifecycleStates]
    /\ issuedVouchers \subseteq VoucherIds

\* Consistency invariant relating voucher state to lifecycle machine state
Consistency ==
    \A v \in VoucherIds :
        /\ (voucherState[v] = Phantom) => (lifecycleState[v] = "pre_issue")
        /\ (voucherState[v] = Valid) => (lifecycleState[v] = "active")
        /\ (voucherState[v] \in {Redeemed, Cancelled}) => (lifecycleState[v] = "terminal")

\* Combined safety invariant
SafetyInvariant == TypeOK /\ Consistency

-----------------------------------------------------------------------------
\* Initial state: all vouchers start in phantom state
Init ==
    /\ voucherState = [v \in VoucherIds |-> Phantom]
    /\ lifecycleState = [v \in VoucherIds |-> "pre_issue"]
    /\ issuedVouchers = {}

-----------------------------------------------------------------------------
\* Action: Issue a voucher (transition from phantom to valid)
Issue(v) ==
    /\ v \in VoucherIds
    /\ voucherState[v] = Phantom
    /\ lifecycleState[v] = "pre_issue"
    /\ voucherState' = [voucherState EXCEPT ![v] = Valid]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "active"]
    /\ issuedVouchers' = issuedVouchers \union {v}

\* Action: Redeem a voucher (transition from valid to redeemed)
Redeem(v) ==
    /\ v \in VoucherIds
    /\ voucherState[v] = Valid
    /\ lifecycleState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = Redeemed]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "terminal"]
    /\ UNCHANGED issuedVouchers

\* Action: Cancel a voucher (transition from valid to cancelled)
Cancel(v) ==
    /\ v \in VoucherIds
    /\ voucherState[v] = Valid
    /\ lifecycleState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = Cancelled]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "terminal"]
    /\ UNCHANGED issuedVouchers

\* Action: Transfer a voucher (stuttering action while voucher remains valid)
\* This represents ownership transfer without changing voucher state
Transfer(v) ==
    /\ v \in VoucherIds
    /\ voucherState[v] = Valid
    /\ lifecycleState[v] = "active"
    /\ UNCHANGED <<voucherState, lifecycleState, issuedVouchers>>

\* Next state relation: disjunction of all possible voucher actions
Next ==
    \E v \in VoucherIds :
        \/ Issue(v)
        \/ Redeem(v)
        \/ Cancel(v)
        \/ Transfer(v)

-----------------------------------------------------------------------------
\* Fairness conditions
\* Weak fairness on Issue ensures vouchers can eventually be issued
\* Weak fairness on terminal actions ensures vouchers can complete their lifecycle
Fairness ==
    /\ \A v \in VoucherIds : WF_vars(Issue(v))
    /\ \A v \in VoucherIds : WF_vars(Redeem(v) \/ Cancel(v))

\* Temporal specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Liveness properties

\* Every issued voucher eventually reaches a terminal state
VoucherEventuallyTerminates ==
    \A v \in VoucherIds :
        (voucherState[v] = Valid) ~> (voucherState[v] \in {Redeemed, Cancelled})

\* A phantom voucher can eventually be issued
VoucherCanBeIssued ==
    \A v \in VoucherIds :
        (voucherState[v] = Phantom) ~> (voucherState[v] = Valid)

-----------------------------------------------------------------------------
\* Theorems (properties that hold under the specification)

\* The conjunction of type correctness and consistency is always preserved
THEOREM Spec => []SafetyInvariant

\* Once a voucher is in a terminal state, it stays there (stability)
TerminalStatesAreStable ==
    \A v \in VoucherIds :
        [](voucherState[v] \in {Redeemed, Cancelled} => 
           [](voucherState[v] \in {Redeemed, Cancelled}))

\* A voucher cannot be both redeemed and cancelled
MutualExclusion ==
    \A v \in VoucherIds :
        ~(voucherState[v] = Redeemed /\ voucherState[v] = Cancelled)

\* Vouchers follow proper lifecycle ordering
ProperLifecycleOrder ==
    \A v \in VoucherIds :
        /\ (voucherState[v] = Valid => v \in issuedVouchers)
        /\ (voucherState[v] \in {Redeemed, Cancelled} => v \in issuedVouchers)

=============================================================================
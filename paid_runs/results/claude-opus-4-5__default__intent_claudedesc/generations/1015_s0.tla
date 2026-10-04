---------------------------- MODULE VoucherLifecycle ----------------------------
\* Voucher Lifecycle System based on RFC 3506
\* Models vouchers transitioning through states from creation to final disposition

EXTENDS Naturals, FiniteSets

CONSTANTS
    Vouchers        \* The fixed set of vouchers in the system

VARIABLES
    voucherState,   \* Function mapping each voucher to its state
    lifecycleState  \* Function mapping each voucher to its lifecycle machine state

\* Voucher states
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

\* Lifecycle machine states
LifecycleStates == {"unstarted", "in_progress", "completed"}

\* Type invariant
TypeOK ==
    /\ voucherState \in [Vouchers -> VoucherStates]
    /\ lifecycleState \in [Vouchers -> LifecycleStates]

\* Safety invariant: voucher states and lifecycle states must be consistent
\* - phantom voucher <=> unstarted lifecycle
\* - valid voucher <=> in_progress lifecycle
\* - redeemed or cancelled voucher <=> completed lifecycle
StateConsistency ==
    \A v \in Vouchers:
        /\ (voucherState[v] = "phantom") <=> (lifecycleState[v] = "unstarted")
        /\ (voucherState[v] = "valid") <=> (lifecycleState[v] = "in_progress")
        /\ (voucherState[v] \in {"redeemed", "cancelled"}) <=> (lifecycleState[v] = "completed")

\* Initial state: all vouchers start in phantom state with unstarted lifecycle
Init ==
    /\ voucherState = [v \in Vouchers |-> "phantom"]
    /\ lifecycleState = [v \in Vouchers |-> "unstarted"]

\* Issue action: transition a voucher from phantom to valid (irreversible)
Issue(v) ==
    /\ voucherState[v] = "phantom"
    /\ lifecycleState[v] = "unstarted"
    /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "in_progress"]

\* Transfer action: no-op for valid voucher (state remains unchanged)
Transfer(v) ==
    /\ voucherState[v] = "valid"
    /\ lifecycleState[v] = "in_progress"
    /\ UNCHANGED <<voucherState, lifecycleState>>

\* Redeem action: transition a valid voucher to redeemed (terminal state)
Redeem(v) ==
    /\ voucherState[v] = "valid"
    /\ lifecycleState[v] = "in_progress"
    /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]

\* Cancel action: transition a valid voucher to cancelled (terminal state)
Cancel(v) ==
    /\ voucherState[v] = "valid"
    /\ lifecycleState[v] = "in_progress"
    /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]

\* Next state relation: any voucher can undergo any applicable transition
Next ==
    \E v \in Vouchers:
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

\* Specification without fairness (deadlock freedom not required)
Spec == Init /\ [][Next]_<<voucherState, lifecycleState>>

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ StateConsistency

\* Auxiliary invariants that follow from the transition rules

\* Once a voucher is redeemed, it stays redeemed
RedeemedIsTerminal ==
    [][\A v \in Vouchers: 
        voucherState[v] = "redeemed" => voucherState'[v] = "redeemed"]_<<voucherState, lifecycleState>>

\* Once a voucher is cancelled, it stays cancelled
CancelledIsTerminal ==
    [][\A v \in Vouchers:
        voucherState[v] = "cancelled" => voucherState'[v] = "cancelled"]_<<voucherState, lifecycleState>>

\* A phantom voucher can only become valid (not directly redeemed or cancelled)
PhantomOnlyToValid ==
    [][\A v \in Vouchers:
        voucherState[v] = "phantom" => 
            voucherState'[v] \in {"phantom", "valid"}]_<<voucherState, lifecycleState>>

\* A valid voucher cannot return to phantom
ValidNeverToPhantom ==
    [][\A v \in Vouchers:
        voucherState[v] = "valid" => voucherState'[v] # "phantom"]_<<voucherState, lifecycleState>>

=============================================================================
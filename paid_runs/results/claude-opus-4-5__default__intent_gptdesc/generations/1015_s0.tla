---------------------------- MODULE VoucherLifecycle ----------------------------
EXTENDS Naturals

CONSTANTS Vouchers

VARIABLES businessState, lifecycleState

\* Business states
NotYetIssued == "NotYetIssued"
Issued == "Issued"
Consumed == "Consumed"
Cancelled == "Cancelled"

BusinessStates == {NotYetIssued, Issued, Consumed, Cancelled}

\* Lifecycle machine states
NotStarted == "NotStarted"
Active == "Active"
Completed == "Completed"

LifecycleStates == {NotStarted, Active, Completed}

\* Type invariant: all states belong to allowed sets
TypeInvariant ==
    /\ \A v \in Vouchers : businessState[v] \in BusinessStates
    /\ \A v \in Vouchers : lifecycleState[v] \in LifecycleStates

\* Consistency invariant: business state and lifecycle state must be consistent
ConsistencyInvariant ==
    \A v \in Vouchers :
        /\ (businessState[v] = NotYetIssued) <=> (lifecycleState[v] = NotStarted)
        /\ (businessState[v] = Issued) <=> (lifecycleState[v] = Active)
        /\ (businessState[v] \in {Consumed, Cancelled}) <=> (lifecycleState[v] = Completed)

\* Terminal state exclusivity: only one terminal state when completed
TerminalStateExclusivity ==
    \A v \in Vouchers :
        lifecycleState[v] = Completed =>
            (businessState[v] = Consumed \/ businessState[v] = Cancelled)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ ConsistencyInvariant
    /\ TerminalStateExclusivity

\* Initial state: all vouchers start unissued with lifecycle not started
Init ==
    /\ businessState = [v \in Vouchers |-> NotYetIssued]
    /\ lifecycleState = [v \in Vouchers |-> NotStarted]

\* Issue action: move voucher from not-yet-issued to issued/active
Issue(v) ==
    /\ businessState[v] = NotYetIssued
    /\ lifecycleState[v] = NotStarted
    /\ businessState' = [businessState EXCEPT ![v] = Issued]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = Active]

\* Transfer action: no-op operation while issued/active (state remains same)
Transfer(v) ==
    /\ businessState[v] = Issued
    /\ lifecycleState[v] = Active
    /\ businessState' = businessState
    /\ lifecycleState' = lifecycleState

\* Redeem action: consume voucher and complete lifecycle
Redeem(v) ==
    /\ businessState[v] = Issued
    /\ lifecycleState[v] = Active
    /\ businessState' = [businessState EXCEPT ![v] = Consumed]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = Completed]

\* Cancel action: invalidate voucher and complete lifecycle
Cancel(v) ==
    /\ businessState[v] = Issued
    /\ lifecycleState[v] = Active
    /\ businessState' = [businessState EXCEPT ![v] = Cancelled]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = Completed]

\* Next state relation
Next ==
    \E v \in Vouchers :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

\* Fairness: weak fairness on all actions for each voucher
Fairness ==
    \A v \in Vouchers :
        /\ WF_<<businessState, lifecycleState>>(Issue(v))
        /\ WF_<<businessState, lifecycleState>>(Redeem(v))
        /\ WF_<<businessState, lifecycleState>>(Cancel(v))

\* System specification with fairness
Spec == Init /\ [][Next]_<<businessState, lifecycleState>> /\ Fairness

\* Liveness properties

\* Issuing is only possible from not-yet-issued state
IssuingOnlyFromNotYetIssued ==
    \A v \in Vouchers :
        [](businessState[v] # NotYetIssued => [][businessState'[v] # Issued \/ businessState[v] = Issued]_<<businessState, lifecycleState>>)

\* Redemption only occurs from issued/active state
RedemptionOnlyFromIssued ==
    \A v \in Vouchers :
        []((businessState'[v] = Consumed /\ businessState[v] # Consumed) => 
           (businessState[v] = Issued /\ lifecycleState[v] = Active))

\* Cancellation only occurs from issued/active state
CancellationOnlyFromIssued ==
    \A v \in Vouchers :
        []((businessState'[v] = Cancelled /\ businessState[v] # Cancelled) => 
           (businessState[v] = Issued /\ lifecycleState[v] = Active))

\* Once completed, voucher remains in terminal state
CompletedIsTerminal ==
    \A v \in Vouchers :
        [](lifecycleState[v] = Completed => 
           [](lifecycleState[v] = Completed /\ businessState[v] \in {Consumed, Cancelled}))

\* Once issued, cannot revert to not-yet-issued
NoRevertToNotYetIssued ==
    \A v \in Vouchers :
        [](businessState[v] # NotYetIssued => [](businessState[v] # NotYetIssued))

\* Every voucher eventually gets issued (if system keeps running with fairness)
EventuallyIssued ==
    \A v \in Vouchers :
        <>(businessState[v] # NotYetIssued)

\* Every issued voucher eventually terminates
EventuallyTerminates ==
    \A v \in Vouchers :
        [](businessState[v] = Issued => <>(lifecycleState[v] = Completed))

=============================================================================
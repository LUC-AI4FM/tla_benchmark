---------------------------- MODULE VoucherLifecycle ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Vouchers

VARIABLES vState, lcState

vars == <<vState, lcState>>

\* Business states
NotIssued   == "not_issued"
Issued      == "issued"
Consumed    == "consumed"
Invalidated == "invalidated"

BusinessStates == {NotIssued, Issued, Consumed, Invalidated}

\* Lifecycle machine states
NotStarted == "not_started"
Active     == "active"
Completed  == "completed"

LifecycleStates == {NotStarted, Active, Completed}

TerminalStates == {Consumed, Invalidated}

-----------------------------------------------------------------------------
Init ==
    /\ vState  = [v \in Vouchers |-> NotIssued]
    /\ lcState = [v \in Vouchers |-> NotStarted]

\* Issue a voucher that has not yet been issued
Issue(v) ==
    /\ vState[v] = NotIssued
    /\ lcState[v] = NotStarted
    /\ vState'  = [vState  EXCEPT ![v] = Issued]
    /\ lcState' = [lcState EXCEPT ![v] = Active]

\* Transfer (or other no-op operation) while issued/active
Transfer(v) ==
    /\ vState[v] = Issued
    /\ lcState[v] = Active
    /\ UNCHANGED vars

\* Redeem: consumes the voucher and completes its lifecycle
Redeem(v) ==
    /\ vState[v] = Issued
    /\ lcState[v] = Active
    /\ vState'  = [vState  EXCEPT ![v] = Consumed]
    /\ lcState' = [lcState EXCEPT ![v] = Completed]

\* Cancel: invalidates the voucher and completes its lifecycle
Cancel(v) ==
    /\ vState[v] = Issued
    /\ lcState[v] = Active
    /\ vState'  = [vState  EXCEPT ![v] = Invalidated]
    /\ lcState' = [lcState EXCEPT ![v] = Completed]

Next ==
    \E v \in Vouchers :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

\* (a) Type correctness
TypeOK ==
    /\ vState  \in [Vouchers -> BusinessStates]
    /\ lcState \in [Vouchers -> LifecycleStates]

\* (b) Consistency between business state and lifecycle-machine state
Consistent ==
    \A v \in Vouchers :
        /\ (vState[v] = NotIssued)  <=> (lcState[v] = NotStarted)
        /\ (vState[v] = Issued)     <=> (lcState[v] = Active)
        /\ (vState[v] \in TerminalStates) <=> (lcState[v] = Completed)

\* Only one terminal state holds when the lifecycle is completed
ExclusiveTerminal ==
    \A v \in Vouchers :
        lcState[v] = Completed =>
            \/ (vState[v] = Consumed    /\ vState[v] # Invalidated)
            \/ (vState[v] = Invalidated /\ vState[v] # Consumed)

Inv == TypeOK /\ Consistent /\ ExclusiveTerminal

-----------------------------------------------------------------------------
\* Temporal (action) properties

\* Once completed, a voucher remains completed in its same terminal state
CompletedIsStable ==
    [][\A v \in Vouchers :
          lcState[v] = Completed =>
              /\ lcState'[v] = Completed
              /\ vState'[v] = vState[v]]_vars

\* Once issued, a voucher never reverts to not-yet-issued
NoRevertToUnissued ==
    [][\A v \in Vouchers :
          vState[v] # NotIssued => vState'[v] # NotIssued]_vars

\* Issuing is only possible from not-yet-issued
IssueOnlyFromNotIssued ==
    [][\A v \in Vouchers :
          (vState'[v] = Issued /\ vState[v] # Issued) =>
              (vState[v] = NotIssued /\ lcState[v] = NotStarted)]_vars

\* Redemption / cancellation only occur from issued/active
TerminateOnlyFromIssued ==
    [][\A v \in Vouchers :
          (vState'[v] \in TerminalStates /\ vState[v] \notin TerminalStates) =>
              (vState[v] = Issued /\ lcState[v] = Active)]_vars

Properties ==
    /\ CompletedIsStable
    /\ NoRevertToUnissued
    /\ IssueOnlyFromNotIssued
    /\ TerminateOnlyFromIssued

THEOREM Spec => []Inv
THEOREM Spec => Properties
=============================================================================
MODULE VoucherLifecycle
EXTENDS Naturals, TLC

CONSTANTS V  \* Set of vouchers

VARIABLES businessState, lifecycleState

BusinessStates == {NotYetIssued, Issued, Consumed, Cancelled}
LifecycleStates == {NotStarted, Active, Completed}

businessToLifecycle ==
  [NotYetIssued |-> NotStarted,
   Issued       |-> Active,
   Consumed     |-> Completed,
   Cancelled    |-> Completed]

Init ==
  /\ businessState \in [V -> BusinessStates]
  /\ lifecycleState \in [V -> LifecycleStates]
  /\ ∀ v ∈ V : businessState[v] = NotYetIssued
              /\ lifecycleState[v] = NotStarted

Issue(v) ==
  /\ v ∈ V
  /\ businessState[v] = NotYetIssued
  /\ lifecycleState[v] = NotStarted
  /\ businessState' = [businessState EXCEPT ![v] = Issued]
  /\ lifecycleState' = [lifecycleState EXCEPT ![v] = Active]

Transfer(v) ==
  /\ v ∈ V
  /\ businessState[v] = Issued
  /\ lifecycleState[v] = Active
  /\ UNCHANGED <<businessState, lifecycleState>>

Redemption(v) ==
  /\ v ∈ V
  /\ businessState[v] = Issued
  /\ lifecycleState[v] = Active
  /\ businessState' = [businessState EXCEPT ![v] = Consumed]
  /\ lifecycleState' = [lifecycleState EXCEPT ![v] = Completed]

Cancellation(v) ==
  /\ v ∈ V
  /\ businessState[v] = Issued
  /\ lifecycleState[v] = Active
  /\ businessState' = [businessState EXCEPT ![v] = Cancelled]
  /\ lifecycleState' = [lifecycleState EXCEPT ![v] = Completed]

Next == ∨∃ v ∈ V : Issue(v) \/ Transfer(v) \/ Redemption(v) \/ Cancellation(v)

InvBusinessStates ==
  ∀ v ∈ V : businessState[v] ∈ BusinessStates

InvLifecycleStates ==
  ∀ v ∈ V : lifecycleState[v] ∈ LifecycleStates

InvConsistency ==
  ∀ v ∈ V : lifecycleState[v] = businessToLifecycle[businessState[v]]

Safety == InvBusinessStates /\ InvLifecycleStates /\ InvConsistency

Spec == Init /\ [][Next]_<<businessState, lifecycleState>> 

END MODULE
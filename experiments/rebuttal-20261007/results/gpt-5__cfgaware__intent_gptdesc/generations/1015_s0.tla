------------------------------ MODULE VoucherLifecycle ------------------------------

EXTENDS Naturals

CONSTANTS
  V,    \* Set of vouchers (given)
  v2    \* A distinguished voucher; must be an element of V

ASSUME v2 \in V

(*
  Business-state atoms:
    - NotYetIssued: initial, voucher not issued/usable yet
    - Issued: voucher issued/usable
    - Consumed: voucher redeemed
    - Cancelled: voucher invalidated/cancelled
  Lifecycle-state atoms:
    - NotStarted: initial lifecycle state
    - Active: lifecycle in progress
    - Completed: lifecycle finished
*)
BusinessStates == {NotYetIssued, Issued, Consumed, Cancelled}
LCStates       == {NotStarted, Active, Completed}

VARIABLES
  bState,   \* function: V -> BusinessStates
  lcState   \* function: V -> LCStates

Vars == << bState, lcState >>

Init ==
  /\ bState \in [V -> {NotYetIssued}]
  /\ lcState \in [V -> {NotStarted}]

Issue(v) ==
  /\ v \in V
  /\ bState[v] = NotYetIssued
  /\ lcState[v] = NotStarted
  /\ bState' = [bState EXCEPT ![v] = Issued]
  /\ lcState' = [lcState EXCEPT ![v] = Active]

Transfer(v) ==
  /\ v \in V
  /\ bState[v] = Issued
  /\ lcState[v] = Active
  /\ UNCHANGED Vars

Redeem(v) ==
  /\ v \in V
  /\ bState[v] = Issued
  /\ lcState[v] = Active
  /\ bState' = [bState EXCEPT ![v] = Consumed]
  /\ lcState' = [lcState EXCEPT ![v] = Completed]

Cancel(v) ==
  /\ v \in V
  /\ bState[v] = Issued
  /\ lcState[v] = Active
  /\ bState' = [bState EXCEPT ![v] = Cancelled]
  /\ lcState' = [lcState EXCEPT ![v] = Completed]

Next ==
  \E v \in V:
    ( Issue(v)
    \/ Transfer(v)
    \/ Redeem(v)
    \/ Cancel(v)
    )

\* Type invariant: states always belong to the allowed sets
VTypeOK ==
  /\ bState \in [V -> BusinessStates]
  /\ lcState \in [V -> LCStates]

\* Consistency invariant between business and lifecycle states
VConsistent ==
  \A v \in V:
    /\ (bState[v] = NotYetIssued) <=> (lcState[v] = NotStarted)
    /\ (bState[v] = Issued)       <=> (lcState[v] = Active)
    /\ (bState[v] \in {Consumed, Cancelled}) <=> (lcState[v] = Completed)

\* Enabledness expectations:
\* - Issuing is possible iff in NotYetIssued/NotStarted.
\* - Redeem/Cancel/Transfer are possible iff in Issued/Active.
EnablednessOK ==
  \A v \in V:
    /\ (ENABLED Issue(v))   <=> (bState[v] = NotYetIssued /\ lcState[v] = NotStarted)
    /\ (ENABLED Redeem(v))  <=> (bState[v] = Issued       /\ lcState[v] = Active)
    /\ (ENABLED Cancel(v))  <=> (bState[v] = Issued       /\ lcState[v] = Active)
    /\ (ENABLED Transfer(v))<=> (bState[v] = Issued       /\ lcState[v] = Active)

VSpec ==
  Init
  /\ [][Next]_Vars
  /\ [] (VTypeOK /\ VConsistent /\ EnablednessOK)

=============================================================================
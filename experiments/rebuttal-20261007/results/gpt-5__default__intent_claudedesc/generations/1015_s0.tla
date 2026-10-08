----------------------------- MODULE VoucherLifecycle -----------------------------
CONSTANTS V \* Fixed set of vouchers

VARIABLES vState, lcState

VoucherStates == {"Phantom", "Valid", "Redeemed", "Cancelled"}
LifecycleStates == {"Unstarted", "InProgress", "Completed"}
TerminalVoucherStates == {"Redeemed", "Cancelled"}

TypeInv ==
  /\ vState \in [V -> VoucherStates]
  /\ lcState \in [V -> LifecycleStates]

LifecycleConsistent ==
  \A v \in V:
    /\ (vState[v] = "Phantom") <=> (lcState[v] = "Unstarted")
    /\ (vState[v] = "Valid") <=> (lcState[v] = "InProgress")
    /\ (vState[v] \in TerminalVoucherStates) <=> (lcState[v] = "Completed")

Init ==
  /\ vState = [v \in V |-> "Phantom"]
  /\ lcState = [v \in V |-> "Unstarted"]

Issue(v) ==
  /\ v \in V
  /\ vState[v] = "Phantom"
  /\ lcState[v] = "Unstarted"
  /\ vState' = [vState EXCEPT ![v] = "Valid"]
  /\ lcState' = [lcState EXCEPT ![v] = "InProgress"]

Transfer(v) ==
  /\ v \in V
  /\ vState[v] = "Valid"
  /\ lcState[v] = "InProgress"
  /\ UNCHANGED <<vState, lcState>>

Redeem(v) ==
  /\ v \in V
  /\ vState[v] = "Valid"
  /\ lcState[v] = "InProgress"
  /\ vState' = [vState EXCEPT ![v] = "Redeemed"]
  /\ lcState' = [lcState EXCEPT ![v] = "Completed"]

Cancel(v) ==
  /\ v \in V
  /\ vState[v] = "Valid"
  /\ lcState[v] = "InProgress"
  /\ vState' = [vState EXCEPT ![v] = "Cancelled"]
  /\ lcState' = [lcState EXCEPT ![v] = "Completed"]

Next ==
  \E v \in V:
    Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

Vars == <<vState, lcState>>

Spec ==
  Init /\ [][Next]_Vars

SafetyInvariant ==
  TypeInv /\ LifecycleConsistent

THEOREM Spec => []SafetyInvariant
=============================================================================
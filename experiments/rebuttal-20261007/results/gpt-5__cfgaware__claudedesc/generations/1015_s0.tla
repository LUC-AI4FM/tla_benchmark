------------------------------ MODULE VoucherRFC3506 ------------------------------

CONSTANTS V, v2

ASSUME v2 \in V

VARIABLES vState, vlcState

VStates == {"phantom", "valid", "redeemed", "cancelled"}
LStates == {"init", "working", "done"}

Init ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

Issue(v) ==
  /\ v \in V
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ v \in V
  /\ vState[v] = "valid"
  /\ vState' = vState
  /\ vlcState' = vlcState

Redeem(v) ==
  /\ v \in V
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ v \in V
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext ==
  \E v \in V:
       Issue(v)
    \/ Transfer(v)
    \/ Redeem(v)
    \/ Cancel(v)

vars == << vState, vlcState >>

VTypeOK ==
  /\ vState \in [V -> VStates]
  /\ vlcState \in [V -> LStates]

VConsistent ==
  \A v \in V:
    /\ (vState[v] = "phantom" <=> vlcState[v] = "init")
    /\ (vState[v] = "valid"   <=> vlcState[v] = "working")
    /\ (vState[v] \in {"redeemed","cancelled"} <=> vlcState[v] = "done")

VSpec == Init /\ [][VNext]_vars

THEOREM VSpec => [](VTypeOK /\ VConsistent)

=============================================================================
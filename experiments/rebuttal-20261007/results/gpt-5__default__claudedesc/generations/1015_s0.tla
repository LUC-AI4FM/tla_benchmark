---- MODULE Vouchers3506 ----
EXTENDS TLC

CONSTANTS V

VARIABLES vState, vlcState

VStatus == {"phantom", "valid", "redeemed", "cancelled"}
VLCStatus == {"init", "working", "done"}

VTypeOK ==
  /\ vState \in [V -> VStatus]
  /\ vlcState \in [V -> VLCStatus]

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

VStep(v) == Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

VNext == \E v \in V: VStep(v)

Vars == << vState, vlcState >>

VSpec == Init /\ [][VNext]_Vars

VConsistent ==
  \A v \in V:
    /\ (vState[v] = "phantom") <=> (vlcState[v] = "init")
    /\ (vState[v] = "valid") <=> (vlcState[v] = "working")
    /\ (vState[v] \in {"redeemed", "cancelled"}) <=> (vlcState[v] = "done")

Next == VNext
Spec == VSpec

THEOREM VSpec => [](VTypeOK /\ VConsistent)

====
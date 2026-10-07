------------------------------ MODULE VoucherLifecycle ------------------------------
EXTENDS Naturals, TLC

CONSTANTS V

VARIABLES vState, vlcState

(* Type invariant *)
VTypeOK == 
  /\ vState \in [V -> {"phantom","valid","redeemed","cancelled"}]
  /\ vlcState \in [V -> {"init","working","done"}]

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

VNext == \E v \in V : (Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v))

Stutter ==
  /\ vState' = vState
  /\ vlcState' = vlcState

Next == VNext \/ Stutter

VConsistent ==
  \A v \in V :
    ((vState[v] = "phantom" /\ vlcState[v] = "init") \/ 
     (vState[v] = "valid"   /\ vlcState[v] = "working") \/ 
     ((vState[v] = "redeemed" \/ vState[v] = "cancelled") /\ vlcState[v] = "done"))

VSpec == Init /\ []Next

THEOREM VSpec => ([]VTypeOK) /\ ([]VConsistent)

=============================================================================
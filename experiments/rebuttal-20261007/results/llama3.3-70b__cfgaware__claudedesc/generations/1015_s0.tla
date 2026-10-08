---------------------------- MODULE VoucherLifeCycle ----------------------------
EXTENDS Integers, TLC

CONSTANT V

VARIABLE vState, vlcState

v2 == [v \in V |-> "phantom"]

VTypeOK == 
  (vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]) /\
  (vlcState \in [V -> {"init", "working", "done"}])

Issue(v) == 
  (vState[v] = "phantom") /\ 
  (vlcState[v] = "init") /\ 
  (vState' = [vState EXCEPT ![v] = "valid"]) /\ 
  (vlcState' = [vlcState EXCEPT ![v] = "working"])

Transfer(v) == 
  (vState[v] = "valid") /\ 
  (vlcState[v] = "working") /\ 
  (vState' = vState) /\ 
  (vlcState' = vlcState)

Redeem(v) == 
  (vState[v] = "valid") /\ 
  (vlcState[v] = "working") /\ 
  (vState' = [vState EXCEPT ![v] = "redeemed"]) /\ 
  (vlcState' = [vlcState EXCEPT ![v] = "done"])

Cancel(v) == 
  (vState[v] = "valid") /\ 
  (vlcState[v] = "working") /\ 
  (vState' = [vState EXCEPT ![v] = "cancelled"]) /\ 
  (vlcState' = [vlcState EXCEPT ![v] = "done"])

VNext == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

VConsistent == 
  \A v \in V : 
    ((vState[v] = "phantom") /\ (vlcState[v] = "init")) \/
    ((vState[v] = "valid") /\ (vlcState[v] = "working")) \/
    (((vState[v] = "redeemed") \/ (vState[v] = "cancelled")) /\ (vlcState[v] = "done"))

VSpec == 
  (vState = v2) /\ (vlcState = [v \in V |-> "init"]) /\ 
  []<<VNext>>_vState /\ []<<VNext>>_vlcState

THEOREM VSpec => []VTypeOK /\ []VConsistent
=============================================================================
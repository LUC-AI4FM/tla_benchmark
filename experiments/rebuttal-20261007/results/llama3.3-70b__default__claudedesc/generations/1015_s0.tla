```tla
MODULE VoucherLifeCycle

EXTENDS Integers, FiniteSets

CONSTANTS V

VARIABLES vState, vlcState

Init ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
  /\ UNCHANGED << >>

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ vState' = vState
  /\ vlcState' = vlcState
  /\ UNCHANGED << >>

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ UNCHANGED << >>

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ UNCHANGED << >>

VNext ==
  \E v \in V :
    Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

Spec == Init /\ [][VNext]_<<vState, vlcState>>

VConsistent ==
  \A v \in V :
    (vState[v] = "phantom") <=> (vlcState[v] = "init")
    /\ (vState[v] = "valid") <=> (vlcState[v] = "working")
    /\ (vState[v] \in {"redeemed", "cancelled"}) <=> (vlcState[v] = "done")

VTypeOK ==
  vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

THEOREM Spec => []VTypeOK /\ []VConsistent

```

Instantiation for model checking:
```tla
V == {v1, v2, v3}
```
MODULE VoucherLifecycle
EXTENDS Naturals

CONSTANTS V

VARIABLE v2

BusinessState == {"not-yet-issued", "issued/usable", "consumed", "invalidated"}
LifeCycleState == {"not-started", "active", "completed"}

Init ==
  /\ v2 \in [V -> [businessState: BusinessState, lifeCycleState: LifeCycleState]]
  /\ \A i \in V : v2[i].businessState = "not-yet-issued" /\ v2[i].lifeCycleState = "not-started"

Issue(v) == 
  /\ v \in V
  /\ v2[v].businessState = "not-yet-issued"
  /\ v2[v].lifeCycleState = "not-started"
  /\ v2' = [v2 EXCEPT ![v].businessState = "issued/usable",
                          ![v].lifeCycleState = "active"]

Transfer(v) ==
  /\ v \in V
  /\ v2[v].businessState = "issued/usable"
  /\ v2[v].lifeCycleState = "active"
  /\ v2' = v2

Redeem(v) ==
  /\ v \in V
  /\ v2[v].businessState = "issued/usable"
  /\ v2[v].lifeCycleState = "active"
  /\ v2' = [v2 EXCEPT ![v].businessState = "consumed",
                          ![v].lifeCycleState = "completed"]

Cancel(v) ==
  /\ v \in V
  /\ v2[v].businessState = "issued/usable"
  /\ v2[v].lifeCycleState = "active"
  /\ v2' = [v2 EXCEPT ![v].businessState = "invalidated",
                          ![v].lifeCycleState = "completed"]

Next == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

VTypeOK ==
  \A v \in V :
    v2[v].businessState \in BusinessState /\ 
    v2[v].lifeCycleState \in LifeCycleState

VConsistent ==
  \A v \in V :
    (v2[v].businessState = "not-yet-issued" /\ v2[v].lifeCycleState = "not-started") \/ 
    (v2[v].businessState = "issued/usable" /\ v2[v].lifeCycleState = "active") \/ 
    ((v2[v].businessState = "consumed" \/ v2[v].businessState = "invalidated") /\ v2[v].lifeCycleState = "completed")

Inv == VTypeOK /\ VConsistent

VSpec ==
  Init
  /\ [][Next]_v2
  /\ []Inv

===============================================================================
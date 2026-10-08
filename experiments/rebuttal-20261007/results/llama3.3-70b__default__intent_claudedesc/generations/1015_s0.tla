```
MODULE VoucherLifecycle
EXTENDS Integers, FiniteSets

CONSTANTS Vouchers, LifecycleStates
VARIABLES voucherState, lifecycleMachineState

Init ==
  /\ voucherState \in [Vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ lifecycleMachineState \in [Vouchers -> {"unstarted", "in_progress", "completed"}]
  /\ voucherState = [v \in Vouchers |-> "phantom"]
  /\ lifecycleMachineState = [v \in Vouchers |-> "unstarted"]

Next ==
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "phantom"
      /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
      /\ lifecycleMachineState' = [lifecycleMachineState EXCEPT ![v] = "in_progress"]
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "valid"
      /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]  \* transfer is a no-op
      /\ lifecycleMachineState' = lifecycleMachineState
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "valid"
      /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
      /\ lifecycleMachineState' = [lifecycleMachineState EXCEPT ![v] = "completed"]
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "valid"
      /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
      /\ lifecycleMachineState' = [lifecycleMachineState EXCEPT ![v] = "completed"]
  \/ \* stuttering step
      voucherState' = voucherState
      /\ lifecycleMachineState' = lifecycleMachineState

Spec ==
  Init /\ [][Next]_<<voucherState, lifecycleMachineState>>

ConsistencyInvariant ==
  \A v \in Vouchers :
    (voucherState[v] = "phantom") <=> (lifecycleMachineState[v] = "unstarted")
    /\ (voucherState[v] = "valid") <=> (lifecycleMachineState[v] = "in_progress")
    /\ (voucherState[v] \in {"redeemed", "cancelled"}) <=> (lifecycleMachineState[v] = "completed")

THEOREM Spec => []ConsistencyInvariant
```
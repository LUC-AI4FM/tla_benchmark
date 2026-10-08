------------------------------ MODULE VoucherLifeCycle ------------------------------
EXTENDS Naturals

CONSTANTS V
VARIABLES vouchers, machineState

VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}
MachineStates == VoucherStates

Init ==
  /\ vouchers \in [V -> VoucherStates]
  /\ machineState \in [V -> MachineStates]
  /\ \A v \in V : vouchers[v] = "phantom" /\ machineState[v] = "phantom"

Issue(v) ==
  /\ v \in V
  /\ vouchers[v] = "phantom"
  /\ vouchers' = [vouchers EXCEPT ![v] = "valid"]
  /\ machineState' = [machineState EXCEPT ![v] = "valid"]

Redeem(v) ==
  /\ v \in V
  /\ vouchers[v] = "valid"
  /\ vouchers' = [vouchers EXCEPT ![v] = "redeemed"]
  /\ machineState' = [machineState EXCEPT ![v] = "redeemed"]

Cancel(v) ==
  /\ v \in V
  /\ vouchers[v] = "valid"
  /\ vouchers' = [vouchers EXCEPT ![v] = "cancelled"]
  /\ machineState' = [machineState EXCEPT ![v] = "cancelled"]

Transfer(v) ==
  /\ v \in V
  /\ vouchers[v] = "valid"
  /\ vouchers' = vouchers
  /\ machineState' = machineState

Next == Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v)

TypeCorrectness ==
  /\ vouchers \in [V -> VoucherStates]
  /\ machineState \in [V -> MachineStates]

Consistency ==
  /\ \A v \in V : vouchers[v] = machineState[v]

Spec == Init /\ []Next

THEOREM TypeAndConsistencyInvariant == Spec => [](TypeCorrectness /\ Consistency)
=============================================================================
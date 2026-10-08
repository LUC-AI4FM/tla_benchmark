MODULE VoucherLifecycle
EXTENDS Naturals, TLC

CONSTANTS VoucherSet

VARIABLES voucherState, machineState

TypeOK == /\ voucherState \in [VoucherSet -> {"phantom","valid","redeemed","cancelled"}]
          /\ machineState \in [VoucherSet -> {"phantom","valid","redeemed","cancelled"}]
          /\ DOMAIN voucherState = VoucherSet
          /\ DOMAIN machineState = VoucherSet

Consistent == voucherState = machineState

Init == /\ TypeOK
        /\ voucherState = [v \in VoucherSet |-> "phantom"]
        /\ machineState = [v \in VoucherSet |-> "phantom"]

Issue(v) ==
  /\ v \in VoucherSet
  /\ voucherState[v] = "phantom"
  /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
  /\ machineState' = [machineState EXCEPT ![v] = "valid"]

Redeem(v) ==
  /\ v \in VoucherSet
  /\ voucherState[v] = "valid"
  /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
  /\ machineState' = [machineState EXCEPT ![v] = "redeemed"]

Cancel(v) ==
  /\ v \in VoucherSet
  /\ voucherState[v] = "valid"
  /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
  /\ machineState' = [machineState EXCEPT ![v] = "cancelled"]

Transfer(v) ==
  /\ v \in VoucherSet
  /\ voucherState[v] = "valid"
  /\ voucherState' = voucherState
  /\ machineState' = machineState

Next == \E v \in VoucherSet :
          (Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v))

Spec == Init /\ [][Next]_<<voucherState,machineState>> /\ TypeOK /\ Consistent

===============================================================================
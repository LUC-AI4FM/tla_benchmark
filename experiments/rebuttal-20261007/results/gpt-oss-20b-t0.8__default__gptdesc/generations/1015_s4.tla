MODULE VoucherLifeCycle
EXTENDS Naturals, TLC

CONSTANTS VoucherIds

States == {"PHANTOM", "VALID", "REDEEMED", "CANCELLED"}

VARIABLES voucherState, machineState

(*------------------------------------------------------------------*)
(* Type correctness invariant *)
TypeOK ==
  \A v \in VoucherIds :
    voucherState[v] \in States /\ machineState[v] \in States

(*------------------------------------------------------------------*)
(* Consistency invariant relating voucher state to life‑cycle machine state *)
Consistent ==
  \A v \in VoucherIds : voucherState[v] = machineState[v]

SafetyInvariant == TypeOK /\ Consistent

(*------------------------------------------------------------------*)
(* Initialisation *)
Init ==
  /\ voucherState \in [VoucherIds -> States]
  /\ machineState \in [VoucherIds -> States]
  /\ \A v \in VoucherIds :
       voucherState[v] = "PHANTOM" /\
       machineState[v] = "PHANTOM"

(*------------------------------------------------------------------*)
(* Actions *)
Issue(v) ==
  /\ v \in VoucherIds
  /\ voucherState[v] = "PHANTOM"
  /\ voucherState' = [voucherState EXCEPT ![v] = "VALID"]
  /\ machineState' = [machineState EXCEPT ![v] = "VALID"]

Redeem(v) ==
  /\ v \in VoucherIds
  /\ voucherState[v] = "VALID"
  /\ voucherState' = [voucherState EXCEPT ![v] = "REDEEMED"]
  /\ machineState' = [machineState EXCEPT ![v] = "REDEEMED"]

Cancel(v) ==
  /\ v \in VoucherIds
  /\ voucherState[v] = "VALID"
  /\ voucherState' = [voucherState EXCEPT ![v] = "CANCELLED"]
  /\ machineState' = [machineState EXCEPT ![v] = "CANCELLED"]

Transfer(v) ==
  /\ v \in VoucherIds
  /\ voucherState[v] = "VALID"
  /\ voucherState' = voucherState
  /\ machineState' = machineState

Next ==
  \E v \in VoucherIds :
      Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v)

(*------------------------------------------------------------------*)
(* Temporal specification *)
Spec == Init /\ [][Next]_<<voucherState, machineState>>

=============================================================================
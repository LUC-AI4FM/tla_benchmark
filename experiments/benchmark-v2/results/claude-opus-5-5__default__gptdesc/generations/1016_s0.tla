---------------------------- MODULE VoucherRedeem ----------------------------
(***************************************************************************)
(* Voucher redemption protocol between voucher holders (H) and voucher     *)
(* collectors (C), coordinated by a voucher transaction provider (VTP),    *)
(* following a simplified Two-Phase Commit style protocol.  Messages are   *)
(* never removed from msgs, so reception is modeled by message presence.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

  --------------------------- MODULE VoucherLifeCycle ----------------------
  (*************************************************************************)
  (* The voucher life-cycle specification that VoucherRedeem implements.   *)
  (*************************************************************************)
  CONSTANT V
  VARIABLES vState, vlcState

  VTypeOK ==
    /\ vState \in [V -> {"valid", "redeemed"}]
    /\ vlcState \in [V -> {"working", "done"}]

  VInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

  VRedeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

  VNext == \E v \in V : VRedeem(v)

  VConsistent ==
    \A v \in V : vlcState[v] = "done" => vState[v] = "redeemed"

  VSpec == VInit /\ [][VNext]_<<vState, vlcState>>
  ==========================================================================
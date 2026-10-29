---------------------------- MODULE VoucherRedeem ----------------------------
(***************************************************************************)
(* Voucher redemption protocol between voucher holders (H) and voucher     *)
(* collectors (C), coordinated by a voucher transaction provider (VTP),    *)
(* using a simplified Two-Phase Commit style protocol.  The set msgs only  *)
(* grows: messages are never removed, so a message is received if it is   *)
(* present in msgs.                                                        *)
(***************************************************************************)
EXTENDS Naturals

  --------------------------- MODULE VoucherLifeCycle ---------------------------
  (*************************************************************************)
  (* The voucher life-cycle specification implemented by the protocol.     *)
  (*************************************************************************)
  CONSTANT V

  VARIABLES vState, vlcState

  VLCTypeOK ==
    /\ vState   \in [V -> {"valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]

  VLCInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

  Transfer(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ UNCHANGED <<vState, vlcState>>

  Redeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState'   = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

  Cancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState'   = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

  VLCNext == \E v \in V : Transfer(v) \/ Redeem(v) \/ Cancel(v)

  VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

  VLCConsistent ==
    \A v \in V : vlcState[v] = "done" => vState[v] \in {"redeemed", "cancelled"}

  THEOREM VLCSpec => [](VLCTypeOK /\ VLCConsistent)
  ===============================================================================
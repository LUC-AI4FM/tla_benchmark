------------------------------ MODULE VoucherRedeem ------------------------------
(***************************************************************************)
(* A voucher redemption protocol between voucher holders (H) and voucher   *)
(* collectors (C), coordinated by a voucher transaction provider (VTP),    *)
(* using a simplified Two-Phase Commit style protocol.                     *)
(*                                                                         *)
(* The global set msgs only grows. Messages are never removed, so a       *)
(* message is "received" when it is present in msgs.                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

    ---------------------------- MODULE VoucherLifeCycle ----------------------------
    (***********************************************************************)
    (* The abstract voucher life-cycle specification.                      *)
    (***********************************************************************)
    CONSTANT V

    VARIABLES vState, vlcState

    VLCTypeOK ==
        /\ vState   \in [V -> {"valid", "redeemed"}]
        /\ vlcState \in [V -> {"working", "done"}]

    VLCInit ==
        /\ vState   = [v \in V |-> "valid"]
        /\ vlcState = [v \in V |-> "working"]

    Redeem(v) ==
        /\ vState[v]   = "valid"
        /\ vlcState[v] = "working"
        /\ vState'   = [vState   EXCEPT ![v] = "redeemed"]
        /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

    Abort(v) ==
        /\ vState[v]   = "valid"
        /\ vlcState[v] = "working"
        /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
        /\ UNCHANGED vState

    VLCNext == \E v \in V : Redeem(v) \/ Abort(v)

    VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

    VLCConsistent ==
        \A v \in V : vState[v] = "redeemed" => vlcState[v] = "done"
    =================================================================================
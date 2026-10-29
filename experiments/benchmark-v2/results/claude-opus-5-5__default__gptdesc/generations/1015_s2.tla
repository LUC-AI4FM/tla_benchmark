------------------------- MODULE VoucherLifeCycle -------------------------
(***************************************************************************)
(* Life cycle of vouchers, based on RFC 3506, with the tuple component     *)
(* decoupled.  Each voucher begins in a newly introduced "phantom" state   *)
(* before issuance.  It may then be issued and become "valid".  A valid    *)
(* voucher may be transferred, which is a stuttering step, or it may be    *)
(* redeemed or cancelled.                                                  *)
(*                                                                         *)
(* vState records the state of each voucher.  vlcState records the state  *)
(* of the life-cycle machine for each voucher.                             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT V          \* The set of vouchers.

VARIABLES vState,   \* vState[v] is the state of voucher v.
          vlcState  \* vlcState[v] is the state of the life-cycle machine
                    \* for voucher v.

vars == <<vState, vlcState>>

---------------------------------------------------------------------------
VTypeOK == /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
           /\ vlcState \in [V -> {"init", "working", "done"}]

VInit == /\ vState = [v \in V |-> "phantom"]
         /\ vlcState = [v \in V |-> "init"]

---------------------------------------------------------------------------
(* A phantom voucher is issued and becomes valid. *)
Issue(v) == /\ vState[v] = "phantom"
            /\ vlcState[v] = "init"
            /\ vState' = [vState EXCEPT ![v] = "valid"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

(* A valid voucher is transferred.  This is a stuttering step. *)
Transfer(v) == /\ vState[v] = "valid"
               /\ UNCHANGED vars

(* A valid voucher is redeemed. *)
Redeem(v) == /\ vState[v] = "valid"
             /\ vlcState[v] = "working"
             /\ vState' = [vState EXCEPT ![v] = "redeemed"]
             /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

(* A valid voucher is cancelled. *)
Cancel(v) == /\ vState[v] = "valid"
             /\ vlcState[v] = "working"
             /\ vState' = [vState EXCEPT ![v] = "cancelled"]
             /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

---------------------------------------------------------------------------
(* Consistency between voucher state and life-cycle machine state. *)
VConsistent ==
  \A v \in V : \/ /\ vlcState[v] = "done"
                  /\ vState[v] \in {"redeemed", "cancelled"}
               \/ /\ vlcState[v] = "init"
                  /\ vState[v] = "phantom"
               \/ /\ vlcState[v] = "working"
                  /\ vState[v] = "valid"

---------------------------------------------------------------------------
VSpec == VInit /\ [][VNext]_vars

Init == VInit
Next == VNext
Spec == VSpec

TypeOK     == VTypeOK
Consistent == VConsistent

THEOREM VSpec => [](VTypeOK /\ VConsistent)
===========================================================================
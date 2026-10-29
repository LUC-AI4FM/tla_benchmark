------------------------- MODULE VoucherLifeCycle -------------------------
(***************************************************************************)
(* Life cycle of vouchers, based on RFC 3506, with the tuple component     *)
(* decoupled.  Each voucher starts in a newly introduced "phantom" state   *)
(* before it is issued.  Once issued it is "valid", and it can then be     *)
(* either "redeemed" or "cancelled".  Transfer is a stuttering action that *)
(* is allowed while the voucher is valid.                                  *)
(***************************************************************************)

CONSTANT V          \* The set of vouchers.

VARIABLES vState,   \* vState[v] is the state of voucher v.
          vlcState  \* vlcState[v] is the state of the life-cycle machine
                    \* for voucher v.

vars == <<vState, vlcState>>

-----------------------------------------------------------------------------
VTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  (*************************************************************************)
  (* Initially every voucher is a phantom and its life-cycle machine is    *)
  (* in its initial state.                                                 *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Voucher actions.                                                        *)
(***************************************************************************)
Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED vars

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext ==
  \E v \in V : Issue(v) \/ Redeem(v) \/ Transfer(v) \/ Cancel(v)

-----------------------------------------------------------------------------
VConsistent ==
  (*************************************************************************)
  (* The consistency invariant relating each voucher's state to the state  *)
  (* of its life-cycle machine.                                            *)
  (*************************************************************************)
  \A v \in V :
     \/ /\ vlcState[v] = "done"
        /\ vState[v] \in {"redeemed", "cancelled"}
     \/ /\ vlcState[v] = "init"
        /\ vState[v] = "phantom"
     \/ /\ vlcState[v] = "working"
        /\ vState[v] = "valid"

VSpec == VInit /\ [][VNext]_vars

(***************************************************************************)
(* Standard names.                                                         *)
(***************************************************************************)
Init == VInit
Next == VNext
Spec == VSpec

TypeOK == VTypeOK
Consistent == VConsistent
Inv == VTypeOK /\ VConsistent

-----------------------------------------------------------------------------
THEOREM VSpec => [](VTypeOK /\ VConsistent)
=============================================================================
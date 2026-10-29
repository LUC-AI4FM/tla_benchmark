---------------------------- MODULE VoucherLifeCycle ----------------------------
(***************************************************************************)
(* Specification of the life cycle of vouchers as defined by RFC 3506.     *)
(* Each voucher v in V has a voucher state vState[v] and a corresponding   *)
(* life-cycle machine state vlcState[v].                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT V   \* The set of vouchers.

VARIABLES vState,   \* vState[v] is the state of voucher v.
          vlcState  \* vlcState[v] is the state of the voucher life-cycle
                    \* machine for voucher v.

vars == <<vState, vlcState>>

-----------------------------------------------------------------------------

VTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

-----------------------------------------------------------------------------

(* Issue: phantom -> valid, init -> working. One-way and irreversible.     *)
Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

(* Transfer: a no-op on the modeled state; the voucher must be valid.      *)
Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

(* Redeem: valid -> redeemed, working -> done.                              *)
Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

(* Cancel: valid -> cancelled, working -> done.                             *)
Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext ==
  \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

-----------------------------------------------------------------------------

(* Safety invariant: strict correspondence between the two state variables. *)
VConsistent ==
  \A v \in V :
    /\ (vState[v] = "phantom") <=> (vlcState[v] = "init")
    /\ (vState[v] = "valid") <=> (vlcState[v] = "working")
    /\ (vState[v] \in {"redeemed", "cancelled"}) <=> (vlcState[v] = "done")

-----------------------------------------------------------------------------

VSpec == VInit /\ [][VNext]_vars

THEOREM VSpec => [](VTypeOK /\ VConsistent)

(***************************************************************************)
(* Model-checking configuration (VoucherLifeCycle.cfg):                    *)
(*   CONSTANT V = {v1, v2, v3}                                             *)
(*   SPECIFICATION VSpec                                                   *)
(*   INVARIANTS VTypeOK VConsistent                                        *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
=============================================================================
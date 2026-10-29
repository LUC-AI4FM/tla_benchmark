------------------------------ MODULE VoucherLifeCycle ------------------------------
(***************************************************************************)
(* Life cycle of vouchers, based on RFC 3506, with the tuple component     *)
(* decoupled.  A voucher starts in a newly introduced "phantom" state      *)
(* before issuance.  It may then become "valid", and from there it is      *)
(* either redeemed or cancelled.  Transfer is a stuttering action that is  *)
(* enabled only while the voucher is valid.                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT V          \* The set of vouchers

VARIABLES vState,   \* vState[v] is the state of voucher v
          vlcState  \* vlcState[v] is the state of the life-cycle machine of v

vars == <<vState, vlcState>>

-----------------------------------------------------------------------------
VTypeOK ==
  /\ vState   \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  /\ vState   = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

-----------------------------------------------------------------------------
Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState'   = [vState   EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED vars

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState'   = [vState   EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState'   = [vState   EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext ==
  \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

-----------------------------------------------------------------------------
VConsistent ==
  \A v \in V :
    /\ (vlcState[v] = "init")    => (vState[v] = "phantom")
    /\ (vlcState[v] = "working") => (vState[v] = "valid")
    /\ (vlcState[v] = "done")    => (vState[v] \in {"redeemed", "cancelled"})

-----------------------------------------------------------------------------
VSpec == VInit /\ [][VNext]_vars

THEOREM VSpec => [](VTypeOK /\ VConsistent)
=============================================================================
------------------------ MODULE VoucherLifeCycle ------------------------
(***************************************************************************)
(* Life cycle of vouchers, based on RFC 3506, with the tuple component     *)
(* decoupled.  A voucher starts in the "phantom" state (before issuance),  *)
(* becomes "valid" when issued, and is then either "redeemed" or           *)
(* "cancelled".  Transfer is a stuttering action while the voucher is      *)
(* valid.  vlcState is the state of the voucher life-cycle machine.        *)
(***************************************************************************)

CONSTANT V          \* The set of vouchers.

VARIABLE vState,    \* vState[v] is the state of voucher v.
         vlcState   \* vlcState[v] is the state of the life-cycle machine for v.

vars == <<vState, vlcState>>

-----------------------------------------------------------------------------

VTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

-----------------------------------------------------------------------------

Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

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

(***************************************************************************)
(* Consistency between voucher state and life-cycle machine state.         *)
(***************************************************************************)
VConsistent ==
  \A v \in V :
    /\ (vlcState[v] = "init")    <=> (vState[v] = "phantom")
    /\ (vlcState[v] = "working") <=> (vState[v] = "valid")
    /\ (vlcState[v] = "done")    <=> (vState[v] \in {"redeemed", "cancelled"})

-----------------------------------------------------------------------------

VSpec == VInit /\ [][VNext]_vars

THEOREM VSpec => [](VTypeOK /\ VConsistent)
=============================================================================
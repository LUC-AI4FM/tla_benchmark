---------------------------- MODULE VoucherLifeCycle ----------------------------
(***************************************************************************)
(* Life cycle of vouchers, based on RFC 3506, with the tuple component     *)
(* decoupled.  Each voucher starts in a "phantom" state, can be issued     *)
(* (becoming "valid"), and can then be redeemed or cancelled.  Transfer    *)
(* is a stuttering action while the voucher is valid.                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT V          \* The set of vouchers

VARIABLES vState,   \* vState[v] is the state of voucher v
          vlcState  \* vlcState[v] is the state of the life-cycle machine for v

vars == <<vState, vlcState>>

VStates   == {"phantom", "valid", "redeemed", "cancelled"}
VLCStates == {"init", "working", "done"}

-----------------------------------------------------------------------------
VTypeOK == /\ vState   \in [V -> VStates]
           /\ vlcState \in [V -> VLCStates]

VInit == /\ vState   = [v \in V |-> "phantom"]
         /\ vlcState = [v \in V |-> "init"]

-----------------------------------------------------------------------------
Issue(v) == /\ vState[v] = "phantom"
            /\ vlcState[v] = "init"
            /\ vState'   = [vState EXCEPT ![v] = "valid"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) == /\ vState[v] = "valid"
               /\ UNCHANGED vars

Redeem(v) == /\ vState[v] = "valid"
             /\ vlcState[v] = "working"
             /\ vState'   = [vState EXCEPT ![v] = "redeemed"]
             /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) == /\ vState[v] = "valid"
             /\ vlcState[v] = "working"
             /\ vState'   = [vState EXCEPT ![v] = "cancelled"]
             /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

-----------------------------------------------------------------------------
VConsistent ==
    \A v \in V : /\ vlcState[v] = "init"    <=> vState[v] = "phantom"
                 /\ vlcState[v] = "working" <=> vState[v] = "valid"
                 /\ vlcState[v] = "done"    <=> vState[v] \in {"redeemed", "cancelled"}

-----------------------------------------------------------------------------
VSpec == VInit /\ [][VNext]_vars

THEOREM VSpec => [](VTypeOK /\ VConsistent)
=============================================================================
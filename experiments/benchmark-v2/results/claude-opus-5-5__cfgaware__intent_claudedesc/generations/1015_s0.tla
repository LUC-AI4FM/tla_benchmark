---------------------------- MODULE VoucherLifecycle ----------------------------
(***************************************************************************)
(* Voucher lifecycle based on RFC 3506. A fixed set of vouchers V moves   *)
(* from phantom -> valid -> (redeemed | cancelled). Transfer is a no-op   *)
(* on a valid voucher. Each voucher's state is mirrored by a lifecycle    *)
(* machine state: init / working / done.                                  *)
(***************************************************************************)

CONSTANT V

VARIABLES vState, vlcState

vars == << vState, vlcState >>

VoucherStates   == {"phantom", "valid", "redeemed", "cancelled"}
LifecycleStates == {"init", "working", "done"}

-----------------------------------------------------------------------------

VTypeOK ==
    /\ vState   \in [V -> VoucherStates]
    /\ vlcState \in [V -> LifecycleStates]

VConsistent ==
    \A v \in V :
        \/ /\ vState[v] = "phantom"
           /\ vlcState[v] = "init"
        \/ /\ vState[v] = "valid"
           /\ vlcState[v] = "working"
        \/ /\ vState[v] \in {"redeemed", "cancelled"}
           /\ vlcState[v] = "done"

-----------------------------------------------------------------------------

VInit ==
    /\ vState   = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]

\* Issue: phantom -> valid (one-way, irreversible)
VIssue(v) ==
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vState'   = [vState   EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

\* Transfer: a no-op on a valid voucher
VTransfer(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ UNCHANGED vars

\* Redeem: valid -> redeemed (terminal)
VRedeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState'   = [vState   EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

\* Cancel: valid -> cancelled (terminal)
VCancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState'   = [vState   EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext ==
    \E v \in V :
        \/ VIssue(v)
        \/ VTransfer(v)
        \/ VRedeem(v)
        \/ VCancel(v)

VSpec == VInit /\ [][VNext]_vars

-----------------------------------------------------------------------------

THEOREM VSpec => [](VTypeOK /\ VConsistent)

=============================================================================
---------------------------- MODULE VoucherCancel ----------------------------
(***************************************************************************)
(* A two-phase-commit style protocol for cancelling vouchers.  It has one  *)
(* coordinator, a set of voucher issuers I, a set of voucher holders H,    *)
(* and a set of vouchers V.                                                *)
(*                                                                         *)
(* Holders and issuers can each decide on their own to prepare or to       *)
(* abort.  A prepared participant tells the coordinator by sending a       *)
(* "prepared" message.  Messages are added to the set msgs and are never   *)
(* removed.                                                                *)
(*                                                                         *)
(* The coordinator commits the cancellation only after it has received     *)
(* "prepared" from every holder and every issuer.  It may abort at any     *)
(* time before it decides.  It tells every participant its decision by     *)
(* broadcasting a "Cancel" message or an "abort" message.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    I    \* The set of voucher issuers

VARIABLES
    vState,     \* vState[v] : the state of voucher v
    vlcState,   \* vlcState[v] : the state of the lifecycle of voucher v
    hState,     \* hState[h] : the state of holder h
    iState,     \* iState[i] : the state of issuer i
    cState,     \* The state of the coordinator
    hPrepared,  \* The holders from which the coordinator has received "prepared"
    iPrepared,  \* The issuers from which the coordinator has received "prepared"
    msgs        \* The set of all messages that have been sent

vars == << vState, vlcState, hState, iState, cState,
           hPrepared, iPrepared, msgs >>

-----------------------------------------------------------------------------
Messages ==
    [type : {"prepared"}, vh : H]
    \cup [type : {"prepared"}, vi : I]
    \cup [type : {"Cancel", "abort"}]

VTPTypeOK ==
    /\ vState    \in [V -> {"valid", "cancelled"}]
    /\ vlcState  \in [V -> {"working", "done"}]
    /\ hState    \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState    \in [I -> {"valid", "prepared", "cancelled", "aborted"}]
    /\ cState    \in {"init", "commit", "abort"}
    /\ hPrepared \subseteq H
    /\ iPrepared \subseteq I
    /\ msgs      \subseteq Messages

VTPInit ==
    /\ vState    = [v \in V |-> "valid"]
    /\ vlcState  = [v \in V |-> "working"]
    /\ hState    = [h \in H |-> "holding"]
    /\ iState    = [i \in I |-> "valid"]
    /\ cState    = "init"
    /\ hPrepared = {}
    /\ iPrepared = {}
    /\ msgs      = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

\* The coordinator receives a "prepared" message from holder h.
CRcvPrepH(h) ==
    /\ cState = "init"
    /\ [type |-> "prepared", vh |-> h] \in msgs
    /\ hPrepared' = hPrepared \cup {h}
    /\ UNCHANGED << vState, vlcState, hState, iState, cState, iPrepared, msgs >>

\* The coordinator receives a "prepared" message from issuer i.
CRcvPrepI(i) ==
    /\ cState = "init"
    /\ [type |-> "prepared", vi |-> i] \in msgs
    /\ iPrepared' = iPrepared \cup {i}
    /\ UNCHANGED << vState, vlcState, hState, iState, cState, hPrepared, msgs >>

\* The coordinator commits. It needs "prepared" from all holders and
\* all issuers. The vouchers are then cancelled.
CCancel ==
    /\ cState = "init"
    /\ hPrepared = H
    /\ iPrepared = I
    /\ cState'   = "commit"
    /\ vState'   = [v \in V |-> "cancelled"]
    /\ vlcState' = [v \in V |-> "done"]
    /\ msgs'     = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED << hState, iState, hPrepared, iPrepared >>

\* The coordinator aborts. The vouchers stay valid.
CAbort ==
    /\ cState = "init"
    /\ cState'   = "abort"
    /\ vlcState' = [v \in V |-> "done"]
    /\ msgs'     = msgs \cup {[type |-> "abort"]}
    /\ UNCHANGED << vState, hState, iState, hPrepared, iPrepared >>

-----------------------------------------------------------------------------
(* Holder actions *)

\* Holder h decides on its own to prepare and tells the coordinator.
HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "prepared", vh |-> h]}
    /\ UNCHANGED << vState, vlcState, iState, cState, hPrepared, iPrepared >>

\* Holder h decides on its own to abort. It must not have prepared yet.
HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, cState, hPrepared, iPrepared, msgs >>

\* Holder h receives the coordinator's "Cancel" decision.
HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, iState, cState, hPrepared, iPrepared, msgs >>

\* Holder h receives the coordinator's "abort" decision.
HRcvAbortMsg(h) ==
    /\ [type |-> "abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, cState, hPrepared, iPrepared, msgs >>

-----------------------------------------------------------------------------
(* Issuer actions *)

\* Issuer i decides on its own to prepare and tells the coordinator.
IPrepare(i) ==
    /\ iState[i] = "valid"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "prepared", vi |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, cState, hPrepared, iPrepared >>

\* Issuer i decides on its own to abort. It must not have prepared yet.
IChooseToAbort(i) ==
    /\ iState[i] = "valid"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, cState, hPrepared, iPrepared, msgs >>

\* Issuer i receives the coordinator's "Cancel" decision.
IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, hState, cState, hPrepared, iPrepared, msgs >>

\* Issuer i receives the coordinator's "abort" decision.
IRcvAbortMsg(i) ==
    /\ [type |-> "abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, cState, hPrepared, iPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
    \/ CCancel
    \/ CAbort
    \/ \E h \in H :
          \/ CRcvPrepH(h)
          \/ HPrepare(h) \/ HChooseToAbort(h)
          \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          \/ CRcvPrepI(i)
          \/ IPrepare(i) \/ IChooseToAbort(i)
          \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

\* The fairness assumptions are stated here. They are kept apart from VTPSpec.
VTPFairness ==
    /\ WF_vars(CCancel)
    /\ \A h \in H : WF_vars(CRcvPrepH(h))
    /\ \A i \in I : WF_vars(CRcvPrepI(i))

VTPFairSpec == VTPSpec /\ VTPFairness

-----------------------------------------------------------------------------
(* Correctness properties *)

\* No holder and issuer reach conflicting final decisions.
VTPConsistent ==
    /\ \A h \in H, i \in I :
          /\ ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
          /\ ~ (hState[h] = "aborted"   /\ iState[i] = "cancelled")
    /\ \A h1, h2 \in H :
          ~ (hState[h1] = "cancelled" /\ hState[h2] = "aborted")
    /\ \A i1, i2 \in I :
          ~ (iState[i1] = "cancelled" /\ iState[i2] = "aborted")

\* A voucher is cancelled only after the coordinator committed, and the
\* coordinator commits only after "prepared" from every holder and issuer.
VTPCancelSafety ==
    \A v \in V :
        vState[v] = "cancelled" =>
            /\ cState = "commit"
            /\ hPrepared = H
            /\ iPrepared = I

\* Liveness: if all holders and issuers have prepared, the coordinator
\* eventually decides. This needs the fairness in VTPFairSpec.
VTPProgress ==
    ( /\ \A h \in H : hState[h] = "prepared"
      /\ \A i \in I : iState[i] = "prepared" )
    ~> (cState \in {"commit", "abort"})

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent /\ VTPCancelSafety)
=============================================================================
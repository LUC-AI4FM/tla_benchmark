----------------------------- MODULE VoucherIssue -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    I    \* The set of voucher issuers

VARIABLES
    vState,        \* vState[v] is the state of voucher v
    vlcState,      \* vlcState[v] is the state of the voucher life cycle machine for v
    hState,        \* hState[h] is the state of voucher holder h
    iState,        \* iState[i] is the state of voucher issuer i
    vtpState,      \* The state of the voucher transaction provider (coordinator)
    vtpHPrepared,  \* The set of holders from which the VTP has received "Prepared"
    vtpIPrepared,  \* The set of issuers from which the VTP has received "Prepared"
    msgs           \* The set of all messages that have been sent

vars == <<vState, vlcState, hState, iState, vtpState,
          vtpHPrepared, vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Voucher life cycle specification (the abstract specification that the  *)
(* protocol-level specification implements).                              *)
(***************************************************************************)

VLCTypeOK ==
    /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
    /\ vState = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]

VLCIssue(v) ==
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

VLCRedeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCCancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCNext ==
    \E v \in V : VLCIssue(v) \/ VLCRedeem(v) \/ VLCCancel(v)

VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Protocol-level specification.                                           *)
(***************************************************************************)

Messages ==
    [type : {"prepared"}, vh : H]
    \cup [type : {"prepared"}, vi : I]
    \cup [type : {"Issue", "abort"}]

VTPTypeOK ==
    /\ VLCTypeOK
    /\ hState \in [H -> {"waiting", "prepared", "holding", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "issued", "aborted"}]
    /\ vtpState \in {"init", "done", "abort"}
    /\ vtpHPrepared \subseteq H
    /\ vtpIPrepared \subseteq I
    /\ msgs \subseteq Messages

VTPInit ==
    /\ VLCInit
    /\ hState = [h \in H |-> "waiting"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpHPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Voucher transaction provider (coordinator) actions *)

VTPRcvPrepared(h, i) ==
    /\ vtpState = "init"
    /\ [type |-> "prepared", vh |-> h] \in msgs
    /\ [type |-> "prepared", vi |-> i] \in msgs
    /\ vtpHPrepared' = vtpHPrepared \cup {h}
    /\ vtpIPrepared' = vtpIPrepared \cup {i}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPIssue(v) ==
    /\ vtpState = "init"
    /\ vtpHPrepared = H
    /\ vtpIPrepared = I
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Issue"]}
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
    /\ UNCHANGED <<hState, iState, vtpHPrepared, vtpIPrepared>>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "abort"
    /\ msgs' = msgs \cup {[type |-> "abort"]}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpHPrepared, vtpIPrepared>>

-----------------------------------------------------------------------------
(* Voucher holder actions *)

HPrepare(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpHPrepared, vtpIPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpHPrepared, vtpIPrepared, msgs>>

HRcvIssueMsg(h) ==
    /\ [type |-> "Issue"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "holding"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpHPrepared, vtpIPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpHPrepared, vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
(* Voucher issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "prepared", vi |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpHPrepared, vtpIPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpHPrepared, vtpIPrepared, msgs>>

IRcvIssueMsg(i) ==
    /\ [type |-> "Issue"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "issued"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpHPrepared, vtpIPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpHPrepared, vtpIPrepared, msgs>>

-----------------------------------------------------------------------------

VTPNext ==
    \/ VTPAbort
    \/ \E v \in V : VTPIssue(v)
    \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvIssueMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvIssueMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Spec == VTPSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK == VTPTypeOK

VTPConsistent ==
    \A i \in I, h \in H :
        /\ ~ (iState[i] = "issued" /\ hState[h] = "aborted")
        /\ ~ (hState[h] = "holding" /\ iState[i] = "aborted")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* The protocol-level specification implements the voucher life cycle      *)
(* specification.                                                          *)
(***************************************************************************)

THEOREM VTPSpec => VLCSpec
=============================================================================
------------------------------ MODULE VoucherIssue ------------------------------
(***************************************************************************)
(* Voucher issuance operation from RFC 3506, modeled as a Two-Phase Commit *)
(* protocol coordinated by the Voucher Transaction Provider (VTP).         *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    V,  \* The set of vouchers
    H,  \* The set of voucher holders
    I   \* The set of voucher issuers

VARIABLES
    vState,       \* vState[v] : state of voucher v ("phantom" or "valid")
    vlcState,     \* vlcState[v] : state of v's lifecycle machine
    hState,       \* hState[h] : state of holder h
    iState,       \* iState[i] : state of issuer i
    vtpState,     \* state of the Voucher Transaction Provider
    vtpTPrepared, \* Prepared messages the VTP has received from holders/issuers
    msgs          \* the set of all messages sent

VTPVars == <<vState, vlcState, hState, iState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
HPrepared == [type : {"Prepared"}, vh : H]
IPrepared == [type : {"Prepared"}, vi : I]
PreparedMsgs == HPrepared \cup IPrepared

Messages == PreparedMsgs \cup [type : {"Issue", "Abort"}]

VTPTypeOK ==
    /\ vState \in [V -> {"phantom", "valid"}]
    /\ vlcState \in [V -> {"init", "working"}]
    /\ hState \in [H -> {"waiting", "prepared", "holding", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "issued", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq PreparedMsgs
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]
    /\ hState = [h \in H |-> "waiting"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvPrepared(m) ==
    /\ vtpState = "init"
    /\ m \in PreparedMsgs
    /\ m \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {m}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPIssue(v) ==
    /\ vtpState = "init"
    /\ vtpTPrepared = PreparedMsgs
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vtpState' = "done"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
    /\ msgs' = msgs \cup {[type |-> "Issue"]}
    /\ UNCHANGED <<hState, iState, vtpTPrepared>>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpTPrepared>>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

HRcvIssueMsg(h) ==
    /\ [type |-> "Issue"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "holding"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

IRcvIssueMsg(i) ==
    /\ [type |-> "Issue"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "issued"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
    \/ VTPAbort
    \/ \E v \in V : VTPIssue(v)
    \/ \E m \in PreparedMsgs : VTPRcvPrepared(m)
    \/ \E h \in H : HPrepare(h) \/ HChooseToAbort(h)
                    \/ HRcvIssueMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I : IPrepare(i) \/ IChooseToAbort(i)
                    \/ IRcvIssueMsg(i) \/ IRcvAbortMsg(i)

-----------------------------------------------------------------------------
VTPConsistent ==
    /\ \A h \in H, i \in I : ~ /\ hState[h] = "holding"
                               /\ iState[i] = "aborted"
    /\ \A h \in H, i \in I : ~ /\ hState[h] = "aborted"
                               /\ iState[i] = "issued"

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec
=============================================================================
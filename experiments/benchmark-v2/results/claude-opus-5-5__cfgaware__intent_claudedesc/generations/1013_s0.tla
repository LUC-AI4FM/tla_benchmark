---------------------------- MODULE VoucherIssue ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS V,   \* The set of vouchers
          H,   \* The set of Voucher Holders
          I    \* The set of Voucher Issuers

VARIABLES vState,        \* vState[v] : state of voucher v
          vlcState,      \* vlcState[v] : life-cycle state of voucher v
          hState,        \* hState[h] : state of holder h
          iState,        \* iState[i] : state of issuer i
          vtpState,      \* state of the Voucher Transaction Provider
          vtpIPrepared,  \* issuers from which the VTP received "Prepared"
          vtpHPrepared,  \* holders from which the VTP received "Prepared"
          msgs           \* set of all messages sent

vars == <<vState, vlcState, hState, iState, vtpState,
          vtpIPrepared, vtpHPrepared, msgs>>

Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vi : I]
  \cup [type : {"Issue", "Abort"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract voucher life-cycle specification (high-level spec).            *)
(***************************************************************************)
VInit ==
  /\ vState   = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

VIssue ==
  /\ \A v \in V : vState[v] = "phantom" /\ vlcState[v] = "init"
  /\ vState'   = [v \in V |-> "valid"]
  /\ vlcState' = [v \in V |-> "working"]

VNext == VIssue

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Two-Phase Commit implementation of the Issue operation.                 *)
(***************************************************************************)
VTPTypeOK ==
  /\ vState \in [V -> {"phantom", "valid"}]
  /\ vlcState \in [V -> {"init", "working"}]
  /\ hState \in [H -> {"waiting", "prepared", "holding", "aborted"}]
  /\ iState \in [I -> {"waiting", "prepared", "issued", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpIPrepared \subseteq I
  /\ vtpHPrepared \subseteq H
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState   = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]
  /\ hState   = [h \in H |-> "waiting"]
  /\ iState   = [i \in I |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpIPrepared = {}
  /\ vtpHPrepared = {}
  /\ msgs = {}

\* VTP actions
VTPRcvHPrepared(h) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ vtpHPrepared' = vtpHPrepared \cup {h}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, vtpIPrepared, msgs>>

VTPRcvIPrepared(i) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vi |-> i] \in msgs
  /\ vtpIPrepared' = vtpIPrepared \cup {i}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, vtpHPrepared, msgs>>

VTPIssue ==
  /\ vtpState = "init"
  /\ vtpHPrepared = H
  /\ vtpIPrepared = I
  /\ vtpState' = "done"
  /\ vState'   = [v \in V |-> "valid"]
  /\ vlcState' = [v \in V |-> "working"]
  /\ msgs' = msgs \cup {[type |-> "Issue"]}
  /\ UNCHANGED <<hState, iState, vtpIPrepared, vtpHPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpIPrepared, vtpHPrepared>>

\* Holder actions
HPrepare(h) ==
  /\ hState[h] = "waiting"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpIPrepared, vtpHPrepared>>

HChooseToAbort(h) ==
  /\ hState[h] = "waiting"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpIPrepared, vtpHPrepared, msgs>>

HRcvIssueMsg(h) ==
  /\ [type |-> "Issue"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "holding"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpIPrepared, vtpHPrepared, msgs>>

HRcvAbortMsg(h) ==
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpIPrepared, vtpHPrepared, msgs>>

\* Issuer actions
IPrepare(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpIPrepared, vtpHPrepared>>

IChooseToAbort(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpIPrepared, vtpHPrepared, msgs>>

IRcvIssueMsg(i) ==
  /\ [type |-> "Issue"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "issued"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpIPrepared, vtpHPrepared, msgs>>

IRcvAbortMsg(i) ==
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpIPrepared, vtpHPrepared, msgs>>

VTPNext ==
  \/ VTPIssue
  \/ VTPAbort
  \/ \E h \in H : VTPRcvHPrepared(h) \/ HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvIssueMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I : VTPRcvIPrepared(i) \/ IPrepare(i) \/ IChooseToAbort(i)
                  \/ IRcvIssueMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
VTPConsistent ==
  /\ \A h \in H, i \in I : ~ (hState[h] = "holding" /\ iState[i] = "aborted")
  /\ \A h \in H, i \in I : ~ (iState[i] = "issued" /\ hState[h] = "aborted")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)
THEOREM VTPSpec => VSpec
=============================================================================
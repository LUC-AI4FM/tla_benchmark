---------------------------- MODULE VoucherIssue ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of Voucher Holders
    I    \* The set of Voucher Issuers

VARIABLES
    vState,       \* vState[v]  : abstract voucher state ("phantom" or "valid")
    hState,       \* hState[h]  : state of Holder h
    iState,       \* iState[i]  : state of Issuer i
    tpState,      \* state of the Voucher Transaction Provider (VTP)
    tpHPrepared,  \* set of Holders from which the VTP has received "Prepared"
    tpIPrepared,  \* set of Issuers from which the VTP has received "Prepared"
    msgs          \* set of all messages sent so far

vars == << vState, hState, iState, tpState, tpHPrepared, tpIPrepared, msgs >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Higher-level voucher lifecycle specification. In the Issue operation   *)
(* a voucher moves from the "phantom" state to the "valid" state.         *)
(***************************************************************************)
VLCTypeOK == vState \in [V -> {"phantom", "valid"}]

VLCInit == vState = [v \in V |-> "phantom"]

VLCIssue(v) ==
    /\ vState[v] = "phantom"
    /\ vState' = [vState EXCEPT ![v] = "valid"]

VLCNext == \E v \in V : VLCIssue(v)

VLCSpec == VLCInit /\ [][VLCNext]_vState

-----------------------------------------------------------------------------
(***************************************************************************)
(* Two-Phase Commit implementation of the Issue operation.                *)
(***************************************************************************)
Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vi : I]
  \cup [type : {"Issue", "Abort"}]

TypeOK ==
  /\ VLCTypeOK
  /\ hState \in [H -> {"waiting", "prepared", "holding", "aborted"}]
  /\ iState \in [I -> {"waiting", "prepared", "issued", "aborted"}]
  /\ tpState \in {"init", "done"}
  /\ tpHPrepared \subseteq H
  /\ tpIPrepared \subseteq I
  /\ msgs \subseteq Messages

Init ==
  /\ vState = [v \in V |-> "phantom"]
  /\ hState = [h \in H |-> "waiting"]
  /\ iState = [i \in I |-> "waiting"]
  /\ tpState = "init"
  /\ tpHPrepared = {}
  /\ tpIPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvHPrepared(h) ==
  /\ tpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ tpHPrepared' = tpHPrepared \cup {h}
  /\ UNCHANGED << vState, hState, iState, tpState, tpIPrepared, msgs >>

VTPRcvIPrepared(i) ==
  /\ tpState = "init"
  /\ [type |-> "Prepared", vi |-> i] \in msgs
  /\ tpIPrepared' = tpIPrepared \cup {i}
  /\ UNCHANGED << vState, hState, iState, tpState, tpHPrepared, msgs >>

VTPIssue(v) ==
  /\ tpState = "init"
  /\ tpHPrepared = H
  /\ tpIPrepared = I
  /\ vState[v] = "phantom"
  /\ tpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ msgs' = msgs \cup {[type |-> "Issue"]}
  /\ UNCHANGED << hState, iState, tpHPrepared, tpIPrepared >>

VTPAbort ==
  /\ tpState = "init"
  /\ tpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, hState, iState, tpHPrepared, tpIPrepared >>

(* Holder actions *)

HPrepare(h) ==
  /\ hState[h] = "waiting"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED << vState, iState, tpState, tpHPrepared, tpIPrepared >>

HChooseToAbort(h) ==
  /\ hState[h] = "waiting"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, iState, tpState, tpHPrepared, tpIPrepared, msgs >>

HRcvIssueMsg(h) ==
  /\ hState[h] = "prepared"
  /\ [type |-> "Issue"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "holding"]
  /\ UNCHANGED << vState, iState, tpState, tpHPrepared, tpIPrepared, msgs >>

HRcvAbortMsg(h) ==
  /\ hState[h] = "prepared"
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, iState, tpState, tpHPrepared, tpIPrepared, msgs >>

(* Issuer actions *)

IPrepare(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
  /\ UNCHANGED << vState, hState, tpState, tpHPrepared, tpIPrepared >>

IChooseToAbort(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << vState, hState, tpState, tpHPrepared, tpIPrepared, msgs >>

IRcvIssueMsg(i) ==
  /\ iState[i] = "prepared"
  /\ [type |-> "Issue"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "issued"]
  /\ UNCHANGED << vState, hState, tpState, tpHPrepared, tpIPrepared, msgs >>

IRcvAbortMsg(i) ==
  /\ iState[i] = "prepared"
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << vState, hState, tpState, tpHPrepared, tpIPrepared, msgs >>

-----------------------------------------------------------------------------
Next ==
  \/ VTPAbort
  \/ \E v \in V : VTPIssue(v)
  \/ \E h \in H : VTPRcvHPrepared(h) \/ HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvIssueMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I : VTPRcvIPrepared(i) \/ IPrepare(i) \/ IChooseToAbort(i)
                  \/ IRcvIssueMsg(i) \/ IRcvAbortMsg(i)

Fairness ==
  /\ WF_vars(VTPAbort)
  /\ \A h \in H : /\ WF_vars(HPrepare(h) \/ HChooseToAbort(h))
                  /\ WF_vars(HRcvIssueMsg(h))
                  /\ WF_vars(HRcvAbortMsg(h))
  /\ \A i \in I : /\ WF_vars(IPrepare(i) \/ IChooseToAbort(i))
                  /\ WF_vars(IRcvIssueMsg(i))
                  /\ WF_vars(IRcvAbortMsg(i))

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety: consistency of Holders and Issuers *)
VTPConsistent ==
  /\ \A h \in H : ~ (hState[h] = "holding" /\ \E i \in I : iState[i] = "aborted")
  /\ \A i \in I : ~ (iState[i] = "issued"  /\ \E h \in H : hState[h] = "aborted")

(* Liveness: every participant eventually reaches a terminal state *)
Termination ==
  <>[] ( /\ tpState = "done"
         /\ \A h \in H : hState[h] \in {"holding", "aborted"}
         /\ \A i \in I : iState[i] \in {"issued", "aborted"} )

THEOREM Spec => [](TypeOK /\ VTPConsistent)

THEOREM FairSpec => Termination

(* Refinement: the 2PC protocol implements the voucher lifecycle spec *)
THEOREM Spec => VLCSpec
=============================================================================
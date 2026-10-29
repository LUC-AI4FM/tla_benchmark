------------------------------ MODULE VoucherIssue ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* set of voucher objects issued in this round
    H,   \* set of voucher holders
    I    \* set of voucher issuers

ASSUME H \cap I = {}

Participants == H \cup I

VARIABLES
    vState,     \* vState[v]   : abstract state of voucher v
    vlcState,   \* vlcState[v] : lifecycle state of voucher v
    hState,     \* hState[h]   : state of holder h in this issuance round
    iState,     \* iState[i]   : state of issuer i in this issuance round
    tmState,    \* coordinator state
    tmPrepared, \* participants from which coordinator received "Prepared"
    msgs        \* set of messages ever broadcast (presence = sent)

vars == << vState, vlcState, hState, iState, tmState, tmPrepared, msgs >>

Messages ==
    [type : {"Prepared"}, p : Participants] \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
TypeOK ==
    /\ vState     \in [V -> {"phantom", "valid"}]
    /\ vlcState   \in [V -> {"init", "working"}]
    /\ hState     \in [H -> {"init", "prepared", "holding", "aborted"}]
    /\ iState     \in [I -> {"init", "prepared", "issued", "aborted"}]
    /\ tmState    \in {"init", "committed", "aborted"}
    /\ tmPrepared \subseteq Participants
    /\ msgs       \subseteq Messages

Init ==
    /\ vState     = [v \in V |-> "phantom"]
    /\ vlcState   = [v \in V |-> "init"]
    /\ hState     = [h \in H |-> "init"]
    /\ iState     = [i \in I |-> "init"]
    /\ tmState    = "init"
    /\ tmPrepared = {}
    /\ msgs       = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

TMRcvPrepared(p) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", p |-> p] \in msgs
    /\ tmPrepared' = tmPrepared \cup {p}
    /\ UNCHANGED << vState, vlcState, hState, iState, tmState, msgs >>

TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = Participants
    /\ tmState' = "committed"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED << vState, vlcState, hState, iState, tmPrepared >>

TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED << vState, vlcState, hState, iState, tmPrepared >>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
    /\ hState[h] = "init"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", p |-> h]}
    /\ UNCHANGED << vState, vlcState, iState, tmState, tmPrepared >>

HChooseToAbort(h) ==
    /\ hState[h] = "init"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, tmState, tmPrepared, msgs >>

HRcvCommitMsg(h) ==
    /\ [type |-> "Commit"] \in msgs
    /\ hState[h] = "prepared"
    /\ hState' = [hState EXCEPT ![h] = "holding"]
    /\ UNCHANGED << vState, vlcState, iState, tmState, tmPrepared, msgs >>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState[h] \in {"init", "prepared"}
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, tmState, tmPrepared, msgs >>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "init"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", p |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, tmState, tmPrepared >>

IChooseToAbort(i) ==
    /\ iState[i] = "init"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, tmState, tmPrepared, msgs >>

IRcvCommitMsg(i) ==
    /\ [type |-> "Commit"] \in msgs
    /\ iState[i] = "prepared"
    /\ iState' = [iState EXCEPT ![i] = "issued"]
    /\ vState' = [v \in V |-> "valid"]
    /\ vlcState' = [v \in V |-> "working"]
    /\ UNCHANGED << hState, tmState, tmPrepared, msgs >>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState[i] \in {"init", "prepared"}
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, tmState, tmPrepared, msgs >>

-----------------------------------------------------------------------------
Next ==
    \/ TMCommit
    \/ TMAbort
    \/ \E p \in Participants : TMRcvPrepared(p)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvCommitMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvCommitMsg(i) \/ IRcvAbortMsg(i)

Fairness ==
    /\ \A h \in H : WF_vars(HRcvCommitMsg(h)) /\ WF_vars(HRcvAbortMsg(h))
    /\ \A i \in I : WF_vars(IRcvCommitMsg(i)) /\ WF_vars(IRcvAbortMsg(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No conflicting holder / issuer endpoint states
VConsistent ==
    \A h \in H, i \in I :
        /\ ~(hState[h] = "holding" /\ iState[i] = "aborted")
        /\ ~(iState[i] = "issued"  /\ hState[h] = "aborted")

\* Coordinator commits only when all participants reported readiness
TMCommitOnlyIfAllPrepared ==
    tmState = "committed" => tmPrepared = Participants

\* Coordinator only records readiness actually signalled by participants
TMPreparedSound ==
    \A p \in tmPrepared : [type |-> "Prepared", p |-> p] \in msgs

\* Commit and Abort are never both broadcast
NoConflictingDecisions ==
    ~([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

\* A valid voucher is only the result of a committed round
VoucherValidity ==
    \A v \in V :
        vState[v] = "valid" => (vlcState[v] = "working" /\ tmState = "committed")

IssuedImpliesValid ==
    (\E i \in I : iState[i] = "issued") => \A v \in V : vState[v] = "valid"

\* Once a voucher is valid, its lifecycle advances consistently (never regresses)
VoucherLifecycleMonotone ==
    [][\A v \in V :
          vState[v] = "valid" => (vState'[v] = "valid" /\ vlcState'[v] = "working")]_vars

\* Coordinator decisions happen only under the proper preparedness conditions
TMDecisionAppropriate ==
    [][(tmState = "init" /\ tmState' = "committed") => tmPrepared = Participants]_vars

\* Coordinator decision is final
TMDecisionStable ==
    [][tmState # "init" => tmState' = tmState]_vars

-----------------------------------------------------------------------------
(* Liveness: all participants eventually see the coordinator's decision *)

CommitSeen ==
    (tmState = "committed") ~>
        (/\ \A h \in H : hState[h] = "holding"
         /\ \A i \in I : iState[i] = "issued")

AbortSeen ==
    (tmState = "aborted") ~>
        (/\ \A h \in H : hState[h] = "aborted"
         /\ \A i \in I : iState[i] = "aborted")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ VConsistent /\ TMCommitOnlyIfAllPrepared
                   /\ TMPreparedSound /\ NoConflictingDecisions
                   /\ VoucherValidity /\ IssuedImpliesValid)
THEOREM Spec => VoucherLifecycleMonotone /\ TMDecisionAppropriate /\ TMDecisionStable
THEOREM Spec => CommitSeen /\ AbortSeen
=============================================================================
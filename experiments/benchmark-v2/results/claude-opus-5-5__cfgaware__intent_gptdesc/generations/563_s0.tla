---- MODULE TwoPhase ----
EXTENDS FiniteSets

CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
  [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

TPInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ tmPrepared' = {}
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState>>

RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
       \/ TMRcvPrepared(r)
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)

Fairness ==
  /\ WF_vars(TMCommit)
  /\ WF_vars(TMAbort)
  /\ \A r \in RM :
       /\ WF_vars(TMRcvPrepared(r))
       /\ WF_vars(RMRcvCommitMsg(r))
       /\ WF_vars(RMRcvAbortMsg(r))

TPSpec == TPInit /\ [][TPNext]_vars /\ Fairness

----------------------------------------------------------------------------
\* Abstract transaction-commit specification (TCommit), defined inline

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] /= "committed"

TCPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

TCDecide(r) ==
  \/ /\ rmState[r] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  \/ /\ rmState[r] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : TCPrepare(r) \/ TCDecide(r)

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

TCommitSpecProperty == TCSpec

----------------------------------------------------------------------------
\* Safety properties

CommitOnlyIfDecided ==
  \A r \in RM : rmState[r] = "committed" => tmState = "committed"

NoConflictingTerminalStates == TCConsistent

PreparedNotAborted ==
  \A r \in tmPrepared : rmState[r] /= "aborted"

SafetyInv ==
  /\ TPTypeOK
  /\ CommitOnlyIfDecided
  /\ NoConflictingTerminalStates
  /\ PreparedNotAborted

\* Liveness properties (under the fairness assumptions in TPSpec)

DecisionEventuallyMade == <>(tmState \in {"committed", "aborted"})

AllReachDecision ==
  /\ (tmState = "committed") ~> (\A r \in RM : rmState[r] = "committed")
  /\ (tmState = "aborted") ~> (\A r \in RM : rmState[r] = "aborted")

Liveness == DecisionEventuallyMade /\ AllReachDecision

THEOREM TPSpec => []SafetyInv
THEOREM TPSpec => TCommitSpecProperty
THEOREM TPSpec => Liveness
====
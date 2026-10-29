---------------------------- MODULE TwoPhase ----------------------------
EXTENDS Naturals, FiniteSets

\* Fixed participant set so no external constant bindings are required.
RM == {"r1", "r2", "r3"}

VARIABLES
  rmState,     \* rmState[r] : state of participant r
  tmState,     \* coordinator state
  tmPrepared,  \* set of participants the coordinator knows are prepared
  msgs         \* set of messages sent so far

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
       [type : {"Prepared"}, rm : RM]
  \cup [type : {"Commit", "Abort"}]

TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
\* Phase 1: participants vote; coordinator collects votes.

RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

-----------------------------------------------------------------------------
\* Phase 2: coordinator decides and broadcasts; participants learn decision.

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState[r] # "committed"
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState[r] # "aborted"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Done ==
  /\ tmState # "init"
  /\ \A r \in RM : rmState[r] \in {"committed", "aborted"}
  /\ UNCHANGED vars

Next ==
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
        \/ RMPrepare(r)
        \/ RMChooseToAbort(r)
        \/ TMRcvPrepared(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r)
  \/ Done

Fairness ==
  /\ WF_vars(TMAbort)
  /\ WF_vars(TMCommit)
  /\ \A r \in RM :
        /\ WF_vars(TMRcvPrepared(r))
        /\ WF_vars(RMRcvCommitMsg(r))
        /\ WF_vars(RMRcvAbortMsg(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Correctness properties

\* Agreement: no participant commits while another aborts.
Consistent ==
  \A r1, r2 \in RM : ~ (rmState[r1] = "aborted" /\ rmState[r2] = "committed")

\* Validity: a commit happens only if every participant voted prepared.
Validity ==
  /\ (\E r \in RM : rmState[r] = "committed") => tmState = "committed"
  /\ tmState = "committed" =>
        \A r \in RM : [type |-> "Prepared", rm |-> r] \in msgs
  /\ \A r \in tmPrepared : [type |-> "Prepared", rm |-> r] \in msgs

\* Decision agreement between coordinator and participants.
DecisionAgreement ==
  \A r \in RM :
     /\ rmState[r] = "committed" => tmState = "committed"

Inv == TypeOK /\ Consistent /\ Validity /\ DecisionAgreement

\* Termination: eventually all participants reach a final decision.
Termination ==
  <>(\A r \in RM : rmState[r] \in {"committed", "aborted"})

=============================================================================
------------------------------ MODULE TwoPhaseCommit ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT RM   \* The set of resource managers

VARIABLES
    rmState,     \* rmState[r] is the state of resource manager r
    tmState,     \* The state of the transaction manager
    tmPrepared,  \* The set of RMs from which the TM has received "Prepared"
    msgs         \* The set of all messages sent (messages are never removed)

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
    [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------------
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

-----------------------------------------------------------------------------------
(* Transaction manager actions *)

\* The TM receives a "Prepared" message from resource manager r.
TMRcvPrepared(r) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", rm |-> r] \in msgs
    /\ tmPrepared' = tmPrepared \cup {r}
    /\ UNCHANGED <<rmState, tmState, msgs>>

\* The TM commits once all RMs have reported that they are prepared.
TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

\* The TM may abort at any point before committing.
TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

-----------------------------------------------------------------------------------
(* Resource manager actions *)

\* RM r prepares and signals readiness to the TM.
RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<tmState, tmPrepared>>

\* RM r unilaterally aborts while still undecided.
RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r receives the TM's Commit decision.
RMRcvCommitMsg(r) ==
    /\ [type |-> "Commit"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r receives the TM's Abort decision.
RMRcvAbortMsg(r) ==
    /\ [type |-> "Abort"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

-----------------------------------------------------------------------------------
Next ==
    \/ TMCommit
    \/ TMAbort
    \/ \E r \in RM :
          \/ TMRcvPrepared(r)
          \/ RMPrepare(r)
          \/ RMChooseToAbort(r)
          \/ RMRcvCommitMsg(r)
          \/ RMRcvAbortMsg(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
(* Safety properties *)

\* Consistency: no RM commits while another aborts.
Consistency ==
    \A r1, r2 \in RM :
        ~ (rmState[r1] = "aborted" /\ rmState[r2] = "committed")

\* Commit validity: a commit happens only if every RM was prepared to commit.
CommitValidity ==
    /\ (\E r \in RM : rmState[r] = "committed")
          => \A r \in RM : rmState[r] \in {"prepared", "committed"}
    /\ (tmState = "committed")
          => \A r \in RM : rmState[r] \in {"prepared", "committed"}

\* The TM only records preparedness from RMs that actually prepared.
TMPreparedValid ==
    \A r \in tmPrepared : [type |-> "Prepared", rm |-> r] \in msgs

\* Commit and Abort decisions are never both issued.
DecisionUnique ==
    ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

Invariants ==
    /\ TypeOK
    /\ Consistency
    /\ CommitValidity
    /\ TMPreparedValid
    /\ DecisionUnique

\* Stability: once an RM has committed or aborted, its decision never changes.
Stability ==
    [][\A r \in RM :
          rmState[r] \in {"committed", "aborted"} => rmState'[r] = rmState[r]]_vars

THEOREM Spec => []Invariants
THEOREM Spec => Stability
===================================================================================
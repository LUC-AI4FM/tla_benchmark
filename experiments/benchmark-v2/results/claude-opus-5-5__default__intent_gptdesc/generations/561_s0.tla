------------------------------ MODULE TwoPhaseCommitFT ------------------------------
(***************************************************************************)
(* Two-phase commit with a transaction manager (coordinator) and a set of  *)
(* resource managers.  Participants and the coordinator may crash and      *)
(* recover.                                                                *)
(*                                                                         *)
(* Failure model:                                                          *)
(*  - Stable state (rmState, tmState) is logged durably and survives a     *)
(*    crash.                                                               *)
(*  - The coordinator's volatile set of received votes (tmPrepared) is     *)
(*    lost if it crashes before deciding.                                  *)
(*  - An RM that crashes while still "working" loses its work.  On         *)
(*    recovery it unilaterally aborts, which counts as a vote to abort.    *)
(*  - Messages are never removed from the set msgs.  This models a network *)
(*    that may reorder, delay and duplicate messages, with retransmission. *)
(***************************************************************************)
CONSTANT RM          \* the set of resource managers

VARIABLES
  rmState,     \* rmState[r] \in {"working","prepared","committed","aborted"}
  rmUp,        \* rmUp[r] = TRUE iff RM r is currently running
  tmState,     \* coordinator decision: "init", "committed", "aborted"
  tmUp,        \* TRUE iff the coordinator is currently running
  tmPrepared,  \* RMs from which the coordinator has received "Prepared"
  msgs         \* set of all messages that have been sent

vars == <<rmState, rmUp, tmState, tmUp, tmPrepared, msgs>>

RMStates == {"working", "prepared", "committed", "aborted"}

Messages ==
       [type : {"Prepared", "Aborted"}, rm : RM]
  \cup [type : {"Prepare", "Commit", "Abort"}]

TypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ rmUp \in [RM -> BOOLEAN]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmUp \in BOOLEAN
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ rmUp = [r \in RM |-> TRUE]
  /\ tmState = "init"
  /\ tmUp = TRUE
  /\ tmPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

TMSendPrepare ==
  /\ tmUp
  /\ tmState = "init"
  /\ [type |-> "Prepare"] \notin msgs
  /\ msgs' = msgs \cup {[type |-> "Prepare"]}
  /\ UNCHANGED <<rmState, rmUp, tmState, tmUp, tmPrepared>>

TMRcvPrepared(r) ==
  /\ tmUp
  /\ tmState = "init"
  /\ r \notin tmPrepared
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, rmUp, tmState, tmUp, msgs>>

TMCommit ==
  /\ tmUp
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, rmUp, tmUp, tmPrepared>>

TMRcvAborted(r) ==
  /\ tmUp
  /\ tmState = "init"
  /\ [type |-> "Aborted", rm |-> r] \in msgs
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, rmUp, tmUp, tmPrepared>>

\* (Re)broadcast of an already logged decision, e.g. after recovery.
TMResendDecision ==
  /\ tmUp
  /\ tmState # "init"
  /\ LET m == IF tmState = "committed" THEN [type |-> "Commit"]
                                       ELSE [type |-> "Abort"]
     IN msgs' = msgs \cup {m}
  /\ UNCHANGED <<rmState, rmUp, tmState, tmUp, tmPrepared>>

TMCrash ==
  /\ tmUp
  /\ tmUp' = FALSE
  /\ tmPrepared' = IF tmState = "init" THEN {} ELSE tmPrepared
  /\ UNCHANGED <<rmState, rmUp, tmState, msgs>>

TMRecover ==
  /\ ~tmUp
  /\ tmUp' = TRUE
  /\ UNCHANGED <<rmState, rmUp, tmState, tmPrepared, msgs>>

-----------------------------------------------------------------------------
(* Resource manager actions *)

\* Local choice: vote to prepare (only after the coordinator asked).
RMPrepare(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ [type |-> "Prepare"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<rmUp, tmState, tmUp, tmPrepared>>

\* Local choice: vote to abort.
RMChooseToAbort(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ msgs' = msgs \cup {[type |-> "Aborted", rm |-> r]}
  /\ UNCHANGED <<rmUp, tmState, tmUp, tmPrepared>>

RMRcvCommit(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "prepared"
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<rmUp, tmState, tmUp, tmPrepared, msgs>>

RMRcvAbort(r) ==
  /\ rmUp[r]
  /\ rmState[r] \in {"working", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<rmUp, tmState, tmUp, tmPrepared, msgs>>

RMCrash(r) ==
  /\ rmUp[r]
  /\ rmUp' = [rmUp EXCEPT ![r] = FALSE]
  /\ UNCHANGED <<rmState, tmState, tmUp, tmPrepared, msgs>>

\* An RM recovering in "working" has lost its work and votes to abort.
\* A prepared RM stays prepared (in doubt) and awaits the decision.
RMRecover(r) ==
  /\ ~rmUp[r]
  /\ rmUp' = [rmUp EXCEPT ![r] = TRUE]
  /\ IF rmState[r] = "working"
       THEN /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
            /\ msgs' = msgs \cup {[type |-> "Aborted", rm |-> r]}
       ELSE UNCHANGED <<rmState, msgs>>
  /\ UNCHANGED <<tmState, tmUp, tmPrepared>>

-----------------------------------------------------------------------------
Next ==
  \/ TMSendPrepare \/ TMCommit \/ TMResendDecision \/ TMCrash \/ TMRecover
  \/ \E r \in RM :
       \/ TMRcvPrepared(r) \/ TMRcvAborted(r)
       \/ RMPrepare(r) \/ RMChooseToAbort(r)
       \/ RMRcvCommit(r) \/ RMRcvAbort(r)
       \/ RMCrash(r) \/ RMRecover(r)

\* Protocol progress steps are weakly fair.  Local voting choices,
\* crashes and recoveries are not forced by fairness.
Fairness ==
  /\ WF_vars(TMSendPrepare)
  /\ WF_vars(TMCommit)
  /\ \A r \in RM :
       /\ WF_vars(TMRcvPrepared(r))
       /\ WF_vars(TMRcvAborted(r))
       /\ WF_vars(RMRcvCommit(r))
       /\ WF_vars(RMRcvAbort(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* (1) Atomicity: no RM is committed while another is aborted.
Consistency ==
  \A r1, r2 \in RM :
    ~ (rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* An RM commits only if the coordinator decided commit.
CommitImpliesDecision ==
  \A r \in RM : rmState[r] = "committed" => tmState = "committed"

\* The coordinator commits only if every RM voted to prepare.
DecisionImpliesVotes ==
  tmState = "committed" =>
    \A r \in RM : [type |-> "Prepared", rm |-> r] \in msgs

\* No RM that voted to abort ever prepares or commits.
AbortVoteRespected ==
  \A r \in RM :
    [type |-> "Aborted", rm |-> r] \in msgs => rmState[r] = "aborted"

Invariants ==
  /\ TypeOK
  /\ Consistency
  /\ CommitImpliesDecision
  /\ DecisionImpliesVotes
  /\ AbortVoteRespected

\* (2) Valid state progression for every RM.
ValidRMTransition(r) ==
  \/ rmState'[r] = rmState[r]
  \/ rmState[r] = "working"  /\ rmState'[r] \in {"prepared", "aborted"}
  \/ rmState[r] = "prepared" /\ rmState'[r] \in {"committed", "aborted"}

ValidProgression == [][\A r \in RM : ValidRMTransition(r)]_vars

\* The coordinator's decision is irrevocable.
TMDecisionStable == [][tmState = "init" \/ tmState' = tmState]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* (3) If every RM votes to prepare and the coordinator does not fail
\*     forever (it is eventually permanently up), then every RM that is
\*     eventually permanently up reaches "committed".
CommitLiveness ==
  ( <>[]tmUp /\ \A r \in RM : <>(rmState[r] = "prepared") )
    => \A r \in RM : (<>[]rmUp[r]) => <>(rmState[r] = "committed")

\* If any participant votes to abort and the coordinator does not fail
\* forever, then the global outcome is abort and every RM that is
\* eventually permanently up reaches "aborted".
AbortLiveness ==
  ( <>[]tmUp /\ <>(\E r \in RM : [type |-> "Aborted", rm |-> r] \in msgs) )
    => /\ <>(tmState = "aborted")
       /\ \A r \in RM : (<>[]rmUp[r]) => <>(rmState[r] = "aborted")

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => ValidProgression /\ TMDecisionStable
THEOREM Spec => CommitLiveness /\ AbortLiveness
=============================================================================
------------------------------- MODULE TCommit -------------------------------
(***************************************************************************)
(* Two-phase commit: a transaction coordinator (TM) and a set of resource  *)
(* managers (RM).  Messages are kept in a set (never deleted), so they may *)
(* be delivered late, more than once, or not at all.  RMs and the TM may   *)
(* crash and recover.  Their decision state is kept on stable storage, so  *)
(* it survives a crash.                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM

VARIABLES
  rmState,     \* rmState[r]: local state of resource manager r
  tmState,     \* coordinator decision state
  tmPrepared,  \* set of RMs from which the TM has received "Prepared"
  msgs,        \* set of messages sent so far
  rmUp,        \* rmUp[r]: TRUE iff r is currently running
  tmUp         \* TRUE iff the coordinator is currently running

vars == <<rmState, tmState, tmPrepared, msgs, rmUp, tmUp>>

RMStates == {"working", "prepared", "committed", "aborted"}
TMStates == {"init", "committed", "aborted"}

Messages ==
       [type : {"Prepared", "VoteAbort"}, rm : RM]
  \cup [type : {"Prepare", "Commit", "Abort"}]

TCTypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ tmState \in TMStates
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages
  /\ rmUp \in [RM -> BOOLEAN]
  /\ tmUp \in BOOLEAN

TCInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}
  /\ rmUp = [r \in RM |-> TRUE]
  /\ tmUp = TRUE

(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)
TMSendPrepare ==
  /\ tmUp
  /\ tmState = "init"
  /\ [type |-> "Prepare"] \notin msgs
  /\ msgs' = msgs \cup {[type |-> "Prepare"]}
  /\ UNCHANGED <<rmState, tmState, tmPrepared, rmUp, tmUp>>

TMRcvPrepared(r) ==
  /\ tmUp
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ r \notin tmPrepared
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs, rmUp, tmUp>>

TMCommit ==
  /\ tmUp
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmUp, tmUp>>

\* The TM aborts after receiving an abort vote, or spontaneously
\* (e.g. on a timeout caused by a suspected participant failure).
TMAbort ==
  /\ tmUp
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmUp, tmUp>>

TMRcvVoteAbort(r) ==
  /\ tmUp
  /\ tmState = "init"
  /\ [type |-> "VoteAbort", rm |-> r] \in msgs
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmUp, tmUp>>

\* After recovery the TM re-broadcasts its (persisted) decision.
TMResendDecision ==
  /\ tmUp
  /\ tmState # "init"
  /\ LET m == IF tmState = "committed" THEN [type |-> "Commit"]
                                       ELSE [type |-> "Abort"]
     IN  /\ m \notin msgs
         /\ msgs' = msgs \cup {m}
  /\ UNCHANGED <<rmState, tmState, tmPrepared, rmUp, tmUp>>

(***************************************************************************)
(* Resource manager actions                                                *)
(***************************************************************************)
RMPrepare(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared, rmUp, tmUp>>

RMChooseToAbort(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ msgs' = msgs \cup {[type |-> "VoteAbort", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared, rmUp, tmUp>>

RMRcvCommitMsg(r) ==
  /\ rmUp[r]
  /\ [type |-> "Commit"] \in msgs
  /\ rmState[r] = "prepared"
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmUp, tmUp>>

RMRcvAbortMsg(r) ==
  /\ rmUp[r]
  /\ [type |-> "Abort"] \in msgs
  /\ rmState[r] \in {"working", "prepared"}
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmUp, tmUp>>

(***************************************************************************)
(* Failures and recovery (decision state is on stable storage)             *)
(***************************************************************************)
RMFail(r) ==
  /\ rmUp[r]
  /\ rmUp' = [rmUp EXCEPT ![r] = FALSE]
  /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, tmUp>>

RMRecover(r) ==
  /\ ~rmUp[r]
  /\ rmUp' = [rmUp EXCEPT ![r] = TRUE]
  /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, tmUp>>

TMFail ==
  /\ tmUp
  /\ tmUp' = FALSE
  /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, rmUp>>

TMRecover ==
  /\ ~tmUp
  /\ tmUp' = TRUE
  /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, rmUp>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
TMProgress ==
  \/ TMSendPrepare
  \/ TMCommit
  \/ TMResendDecision
  \/ \E r \in RM : TMRcvPrepared(r) \/ TMRcvVoteAbort(r)

TCNext ==
  \/ TMProgress
  \/ TMAbort
  \/ TMFail
  \/ TMRecover
  \/ \E r \in RM :
        \/ RMPrepare(r) \/ RMChooseToAbort(r)
        \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
        \/ RMFail(r) \/ RMRecover(r)

Fairness ==
  /\ WF_vars(TMProgress)
  /\ WF_vars(TMRecover)
  /\ \A r \in RM :
        /\ WF_vars(RMRcvCommitMsg(r))
        /\ WF_vars(RMRcvAbortMsg(r))
        /\ WF_vars(RMRecover(r))

TCSpec == TCInit /\ [][TCNext]_vars /\ Fairness

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
\* (1) Atomicity
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

\* Commit requires that every RM has prepared.
CommitOnlyIfAllPrepared ==
  (\E r \in RM : rmState[r] = "committed") =>
     \A r \in RM : rmState[r] \in {"prepared", "committed"}

\* Coordinator decision is consistent with participant states.
DecisionConsistent ==
  /\ (tmState = "committed") => \A r \in RM : rmState[r] # "aborted"
  /\ (tmState = "aborted")   => \A r \in RM : rmState[r] # "committed"

\* (2) Valid state progression (action property).
AllowedStep(old, new) ==
  \/ old = new
  \/ old = "working"  /\ new \in {"prepared", "aborted"}
  \/ old = "prepared" /\ new \in {"committed", "aborted"}

TCValidProgression ==
  [][\A r \in RM : AllowedStep(rmState[r], rmState'[r])]_rmState

\* A vote to abort forces a global abort.
AbortVoteImpliesAbort ==
  \A r \in RM :
     ([type |-> "VoteAbort", rm |-> r] \in msgs) => (tmState # "committed")

AbortVoteLeadsToAbort ==
  \A r \in RM :
     ([type |-> "VoteAbort", rm |-> r] \in msgs) ~>
        (\A s \in RM : rmState[s] = "aborted")

\* (3) Termination: if all RMs prepare and the TM commits, all RMs commit;
\* every RM eventually reaches a final state once a decision has been made.
TCTermination ==
  (tmState = "committed") ~> (\A r \in RM : rmState[r] = "committed")

TCEventualDecision ==
  (tmState # "init") ~>
     (\A r \in RM : rmState[r] \in {"committed", "aborted"})

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
==============================================================================
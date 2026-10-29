------------------------------- MODULE TCommitCoordinator -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT RM          \* The finite set of participating resource managers

\* A concrete value for RM, usable from the model configuration (e.g. RM <- RMVal)
RMVal == {"r1", "r2", "r3"}

VARIABLES
    rmState,     \* persisted state of each RM: "working","prepared","committed","aborted"
    rmUp,        \* volatile: TRUE iff the RM is currently running (not crashed)
    tmState,     \* persisted coordinator decision: "init","committed","aborted"
    tmPrepared,  \* set of RMs from which the coordinator has received a Prepared vote
    msgs         \* set of messages in transit (set => delay/duplication; loss via LoseMsg)

vars == <<rmState, rmUp, tmState, tmPrepared, msgs>>

Messages ==
    [type : {"Prepared", "VoteAbort"}, rm : RM]
      \cup [type : {"Prepare", "Commit", "Abort"}]

-----------------------------------------------------------------------------------------
TCTypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ rmUp \in [RM -> BOOLEAN]
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \subseteq RM
    /\ msgs \subseteq Messages

TCInit ==
    /\ rmState = [r \in RM |-> "working"]
    /\ rmUp = [r \in RM |-> TRUE]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------------------
(* Coordinator actions *)

TMSendPrepare ==
    /\ tmState = "init"
    /\ msgs' = msgs \cup {[type |-> "Prepare"]}
    /\ UNCHANGED <<rmState, rmUp, tmState, tmPrepared>>

TMRcvPrepared(r) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", rm |-> r] \in msgs
    /\ tmPrepared' = tmPrepared \cup {r}
    /\ UNCHANGED <<rmState, rmUp, tmState, msgs>>

\* Commit only if every participant has voted Prepared
TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<rmState, rmUp, tmPrepared>>

\* Abort upon a negative vote
TMRcvVoteAbort(r) ==
    /\ tmState = "init"
    /\ [type |-> "VoteAbort", rm |-> r] \in msgs
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, rmUp, tmPrepared>>

\* Timeout: coordinator gives up waiting for votes and aborts
TMTimeoutAbort ==
    /\ tmState = "init"
    /\ tmPrepared # RM
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, rmUp, tmPrepared>>

\* Recovery: coordinator re-broadcasts its persisted decision (handles lost messages)
TMResendDecision ==
    /\ tmState # "init"
    /\ msgs' = msgs \cup {IF tmState = "committed" THEN [type |-> "Commit"]
                                                   ELSE [type |-> "Abort"]}
    /\ UNCHANGED <<rmState, rmUp, tmState, tmPrepared>>

-----------------------------------------------------------------------------------------
(* Resource manager actions *)

RMPrepare(r) ==
    /\ rmUp[r]
    /\ rmState[r] = "working"
    /\ [type |-> "Prepare"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<rmUp, tmState, tmPrepared>>

\* Participant votes to abort (unilateral abort while still working)
RMChooseAbort(r) ==
    /\ rmUp[r]
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ msgs' = msgs \cup {[type |-> "VoteAbort", rm |-> r]}
    /\ UNCHANGED <<rmUp, tmState, tmPrepared>>

RMRcvCommit(r) ==
    /\ rmUp[r]
    /\ rmState[r] \in {"prepared", "committed"}
    /\ [type |-> "Commit"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<rmUp, tmState, tmPrepared, msgs>>

RMRcvAbort(r) ==
    /\ rmUp[r]
    /\ rmState[r] \in {"working", "prepared", "aborted"}
    /\ [type |-> "Abort"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<rmUp, tmState, tmPrepared, msgs>>

\* Timeout/recovery: a prepared (uncertain) RM re-sends its vote to solicit the decision
RMResendVote(r) ==
    /\ rmUp[r]
    /\ rmState[r] = "prepared"
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<rmState, rmUp, tmState, tmPrepared>>

\* Crash: volatile state lost; persisted rmState retained
RMCrash(r) ==
    /\ rmUp[r]
    /\ rmUp' = [rmUp EXCEPT ![r] = FALSE]
    /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs>>

\* Recovery from persisted state; an RM that had not yet prepared may abort on recovery
RMRecover(r) ==
    /\ ~rmUp[r]
    /\ rmUp' = [rmUp EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs>>

-----------------------------------------------------------------------------------------
(* Network: messages may be lost (never corrupted) *)

LoseMsg ==
    /\ \E m \in msgs : msgs' = msgs \ {m}
    /\ UNCHANGED <<rmState, rmUp, tmState, tmPrepared>>

-----------------------------------------------------------------------------------------
TCNext ==
    \/ TMSendPrepare
    \/ TMCommit
    \/ TMTimeoutAbort
    \/ TMResendDecision
    \/ LoseMsg
    \/ \E r \in RM :
          \/ TMRcvPrepared(r)
          \/ TMRcvVoteAbort(r)
          \/ RMPrepare(r)
          \/ RMChooseAbort(r)
          \/ RMRcvCommit(r)
          \/ RMRcvAbort(r)
          \/ RMResendVote(r)
          \/ RMCrash(r)
          \/ RMRecover(r)

TCFairness ==
    /\ WF_vars(TMSendPrepare)
    /\ WF_vars(TMCommit)
    /\ SF_vars(TMResendDecision)
    /\ \A r \in RM :
          /\ WF_vars(RMRecover(r))
          /\ SF_vars(TMRcvPrepared(r))
          /\ SF_vars(TMRcvVoteAbort(r))
          /\ SF_vars(RMPrepare(r))
          /\ SF_vars(RMRcvCommit(r))
          /\ SF_vars(RMRcvAbort(r))
          /\ WF_vars(RMResendVote(r))

TCSpec == TCInit /\ [][TCNext]_vars /\ TCFairness

-----------------------------------------------------------------------------------------
(* Safety: no conflicting terminal decisions *)
TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

(* Coordinator decision agrees with every participant's terminal state *)
TCDecisionConsistent ==
    /\ (tmState = "committed") => \A r \in RM : rmState[r] # "aborted"
    /\ (\E r \in RM : rmState[r] = "committed") => tmState = "committed"

(* Validity: commit only if every participant voted to commit *)
TCValidity ==
    /\ (tmState = "committed") => \A r \in RM : rmState[r] \in {"prepared", "committed"}
    /\ (\E r \in RM : [type |-> "VoteAbort", rm |-> r] \in msgs) => tmState # "committed"

(* Liveness: every non-crashed participant eventually decides, consistently *)
TCTermination ==
    <>(\A r \in RM : rmUp[r] => rmState[r] \in {"committed", "aborted"})

TCAgreement ==
    <>[](\/ \A r \in RM : rmState[r] = "committed"
         \/ \A r \in RM : rmState[r] = "aborted")

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=========================================================================================
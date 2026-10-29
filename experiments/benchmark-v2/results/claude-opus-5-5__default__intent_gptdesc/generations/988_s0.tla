------------------------------ MODULE AtomicCommitFT ------------------------------
(***************************************************************************)
(* An atomic commit protocol for a fixed set of cohorts (resource          *)
(* managers) coordinated by a transaction manager.  The model includes:    *)
(*   - asynchronous, interleaved steps of cohorts and coordinator          *)
(*   - an unordered message pool, so delivery order is arbitrary           *)
(*   - message loss, with retries (re-sends) to recover from it            *)
(*   - crash and recovery of cohorts and the coordinator; decisions and    *)
(*     votes are kept in stable storage and survive crashes                *)
(*   - coordinator timeout leading to a unilateral abort                   *)
(*   - nondeterministic initial cohort states (working or already aborted) *)
(* It states the safety properties validity, agreement and decision        *)
(* permanence. It also states liveness under fairness, assuming that every *)
(* process is eventually responsive forever.                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS RM            \* the set of participants (cohorts)

ASSUME RM # {}

VARIABLES
    rmState,     \* rmState[r] \in {"working","prepared","committed","aborted"}
    tmState,     \* coordinator decision: "init", "committed", "aborted"
    tmPrepared,  \* cohorts from which the coordinator received Prepared
    msgs,        \* unordered pool of messages in transit (reordering / loss)
    rmUp,        \* rmUp[r] = TRUE iff cohort r is currently not crashed
    tmUp         \* TRUE iff the coordinator is currently not crashed

vars == <<rmState, tmState, tmPrepared, msgs, rmUp, tmUp>>

Messages ==
    [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

Decided(r) == rmState[r] \in {"committed", "aborted"}

TypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \subseteq RM
    /\ msgs \subseteq Messages
    /\ rmUp \in [RM -> BOOLEAN]
    /\ tmUp \in BOOLEAN

(***************************************************************************)
(* Initial states: each cohort nondeterministically starts working or      *)
(* already unilaterally aborted (e.g. a local failure before voting).      *)
(***************************************************************************)
Init ==
    /\ rmState \in [RM -> {"working", "aborted"}]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}
    /\ rmUp = [r \in RM |-> TRUE]
    /\ tmUp = TRUE

(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)
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

\* Timeout or explicit abort: the coordinator may abort at any time before
\* it has committed.
TMAbort ==
    /\ tmUp
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, tmPrepared, rmUp, tmUp>>

\* Retry: re-broadcast the decision if it was lost.
TMResendDecision ==
    /\ tmUp
    /\ tmState # "init"
    /\ LET m == IF tmState = "committed" THEN [type |-> "Commit"]
                                         ELSE [type |-> "Abort"]
       IN /\ m \notin msgs
          /\ msgs' = msgs \cup {m}
    /\ UNCHANGED <<rmState, tmState, tmPrepared, rmUp, tmUp>>

TMCrash ==
    /\ tmUp
    /\ tmUp' = FALSE
    /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, rmUp>>

\* The decision and tmPrepared are kept in stable storage.
TMRecover ==
    /\ ~tmUp
    /\ tmUp' = TRUE
    /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, rmUp>>

(***************************************************************************)
(* Cohort actions                                                          *)
(***************************************************************************)
RMPrepare(r) ==
    /\ rmUp[r]
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<tmState, tmPrepared, rmUp, tmUp>>

\* A cohort that has not voted may unilaterally abort.
RMChooseToAbort(r) ==
    /\ rmUp[r]
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs, rmUp, tmUp>>

\* Retry: re-send the Prepared vote while still uncertain.
RMResendPrepared(r) ==
    /\ rmUp[r]
    /\ rmState[r] = "prepared"
    /\ [type |-> "Prepared", rm |-> r] \notin msgs
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<rmState, tmState, tmPrepared, rmUp, tmUp>>

RMRcvCommit(r) ==
    /\ rmUp[r]
    /\ [type |-> "Commit"] \in msgs
    /\ rmState[r] # "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs, rmUp, tmUp>>

RMRcvAbort(r) ==
    /\ rmUp[r]
    /\ [type |-> "Abort"] \in msgs
    /\ rmState[r] # "aborted"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs, rmUp, tmUp>>

RMCrash(r) ==
    /\ rmUp[r]
    /\ rmUp' = [rmUp EXCEPT ![r] = FALSE]
    /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, tmUp>>

\* The local state (vote / decision) is kept in stable storage.
RMRecover(r) ==
    /\ ~rmUp[r]
    /\ rmUp' = [rmUp EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs, tmUp>>

(***************************************************************************)
(* Network: arbitrary loss of in-flight messages. Reordering is implicit   *)
(* because msgs is an unordered set.                                       *)
(***************************************************************************)
LoseMsg ==
    /\ \E m \in msgs : msgs' = msgs \ {m}
    /\ UNCHANGED <<rmState, tmState, tmPrepared, rmUp, tmUp>>

Next ==
    \/ TMCommit \/ TMAbort \/ TMResendDecision \/ TMCrash \/ TMRecover
    \/ LoseMsg
    \/ \E r \in RM :
          \/ TMRcvPrepared(r)
          \/ RMPrepare(r) \/ RMChooseToAbort(r) \/ RMResendPrepared(r)
          \/ RMRcvCommit(r) \/ RMRcvAbort(r)
          \/ RMCrash(r) \/ RMRecover(r)

(***************************************************************************)
(* Fairness: protocol steps of responsive processes are not postponed      *)
(* forever. Receive actions use strong fairness because message loss and   *)
(* crashes may disable them intermittently. Crashes and message loss carry *)
(* no fairness condition.                                                  *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(TMCommit \/ TMAbort)
    /\ WF_vars(TMResendDecision)
    /\ SF_vars(TMRecover)
    /\ \A r \in RM :
          /\ SF_vars(RMPrepare(r) \/ RMChooseToAbort(r))
          /\ SF_vars(RMResendPrepared(r))
          /\ SF_vars(TMRcvPrepared(r))
          /\ SF_vars(RMRcvCommit(r))
          /\ SF_vars(RMRcvAbort(r))
          /\ SF_vars(RMRecover(r))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Validity: a cohort may commit only if every cohort voted Prepared and
\* the coordinator collected all votes and decided commit.
Validity ==
    (\E r \in RM : rmState[r] = "committed") =>
        /\ tmState = "committed"
        /\ tmPrepared = RM

\* A commit decision implies that no cohort is still working or able to
\* abort unilaterally.
CommitRequiresAllPrepared ==
    tmState = "committed" =>
        \A r \in RM : rmState[r] \in {"prepared", "committed"}

NonFaulty == {r \in RM : rmUp[r]}

\* Agreement: no two non-faulty cohorts decide differently.
Agreement ==
    \A r1, r2 \in NonFaulty :
        ~(rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* The stronger form also holds: it covers crashed cohorts, because their
\* decisions are kept in stable storage.
StrongAgreement ==
    \A r1, r2 \in RM :
        ~(rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* The coordinator's decision agrees with the cohorts' decisions.
TMConsistency ==
    \A r \in RM :
        /\ rmState[r] = "committed" => tmState = "committed"
        /\ (rmState[r] = "aborted" /\ tmState # "init") => tmState = "aborted"

Invariants ==
    /\ TypeOK
    /\ Validity
    /\ CommitRequiresAllPrepared
    /\ Agreement
    /\ StrongAgreement
    /\ TMConsistency

\* Decision permanence: once a cohort decides, that decision never changes.
DecisionPermanence ==
    [][\A r \in RM :
         /\ (rmState[r] = "committed" => rmState'[r] = "committed")
         /\ (rmState[r] = "aborted"   => rmState'[r] = "aborted")]_vars

TMDecisionPermanence ==
    [][ /\ (tmState = "committed" => tmState' = "committed")
        /\ (tmState = "aborted"   => tmState' = "aborted")]_vars

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
AllDecided == \A r \in RM : Decided(r)

Unanimous ==
    \/ \A r \in RM : rmState[r] = "committed"
    \/ \A r \in RM : rmState[r] = "aborted"

EventuallyResponsive == <>[](tmUp /\ \A r \in RM : rmUp[r])

\* If the coordinator and every cohort are eventually responsive forever,
\* then all of them reach the same decision and keep it.
Termination ==
    EventuallyResponsive => <>[](AllDecided /\ Unanimous)

\* The coordinator eventually decides, provided that it is eventually
\* responsive forever.
TMTermination ==
    <>[]tmUp => <>(tmState # "init")

THEOREM Spec => []Invariants
THEOREM Spec => DecisionPermanence /\ TMDecisionPermanence
THEOREM Spec => Termination /\ TMTermination
=============================================================================
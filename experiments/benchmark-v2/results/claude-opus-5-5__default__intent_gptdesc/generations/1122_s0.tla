---------------------------- MODULE TwoPhaseCommitBackup ----------------------------
(***************************************************************************)
(* Two-phase commit with a primary transaction manager (TM), a backup     *)
(* transaction manager (BTM), and crash failures of resource managers     *)
(* (RMs) and of the primary TM.                                           *)
(*                                                                         *)
(* RM local states:                                                       *)
(*   "working"   : doing local work                                       *)
(*   "prepared"  : voted to commit, awaiting the global decision          *)
(*   "committed" : terminal, applied the commit decision                  *)
(*   "aborted"   : terminal, aborted unilaterally or by decision          *)
(*   "failed"    : terminal, fail-stop crash from a non-terminal state    *)
(*                                                                         *)
(* TM states: "init", "commit", "abort", or "hidden" (crashed/unavailable)*)
(* BTM states: "init", "commit", "abort".                                 *)
(* The BTM may only act once the primary TM is hidden, and it decides     *)
(* solely from the observable RM states.                                  *)
(*                                                                         *)
(* tmDecision is a history variable that records the decision the TM made *)
(* before possibly crashing. It is used only to state properties.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM

ASSUME RM # {}

VARIABLES rmState, tmState, btmState, tmDecision

vars == <<rmState, tmState, btmState, tmDecision>>

RMStates       == {"working", "prepared", "committed", "aborted", "failed"}
TerminalStates == {"committed", "aborted", "failed"}

TypeOK ==
    /\ rmState    \in [RM -> RMStates]
    /\ tmState    \in {"init", "commit", "abort", "hidden"}
    /\ btmState   \in {"init", "commit", "abort"}
    /\ tmDecision \in {"none", "commit", "abort"}

-----------------------------------------------------------------------------
(* Observations of participant states *)

AllPrepared      == \A r \in RM : rmState[r] = "prepared"
SomeCommitted    == \E r \in RM : rmState[r] = "committed"
SomeAbortOrFail  == \E r \in RM : rmState[r] \in {"aborted", "failed"}

(* The decision visible to participants *)
CommitVisible == tmState = "commit" \/ btmState = "commit"
AbortVisible  == tmState = "abort"  \/ btmState = "abort"

-----------------------------------------------------------------------------
Init ==
    /\ rmState    = [r \in RM |-> "working"]
    /\ tmState    = "init"
    /\ btmState   = "init"
    /\ tmDecision = "none"

-----------------------------------------------------------------------------
(* Resource manager actions *)

RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ UNCHANGED <<tmState, btmState, tmDecision>>

(* Unilateral abort before preparing *)
RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, btmState, tmDecision>>

RMRcvCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ CommitVisible
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, btmState, tmDecision>>

RMRcvAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ AbortVisible
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, btmState, tmDecision>>

(* Fail-stop crash: at most once, only from a non-terminal state, and the *)
(* failed state is absorbing.                                             *)
RMFail(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ rmState' = [rmState EXCEPT ![r] = "failed"]
    /\ UNCHANGED <<tmState, btmState, tmDecision>>

RMProgress(r) == RMPrepare(r) \/ RMRcvCommit(r) \/ RMRcvAbort(r)

-----------------------------------------------------------------------------
(* Primary transaction manager actions *)

TMCommit ==
    /\ tmState = "init"
    /\ AllPrepared
    /\ tmState'    = "commit"
    /\ tmDecision' = "commit"
    /\ UNCHANGED <<rmState, btmState>>

TMAbort ==
    /\ tmState = "init"
    /\ SomeAbortOrFail
    /\ tmState'    = "abort"
    /\ tmDecision' = "abort"
    /\ UNCHANGED <<rmState, btmState>>

TMDecide == TMCommit \/ TMAbort

(* The TM may crash at any time, including after deciding but before any *)
(* RM has observed the decision. After the crash its state is hidden.     *)
TMCrash ==
    /\ tmState # "hidden"
    /\ tmState' = "hidden"
    /\ UNCHANGED <<rmState, btmState, tmDecision>>

-----------------------------------------------------------------------------
(* Backup transaction manager actions *)

(* Commit is safe if some RM already committed (so the primary decided     *)
(* commit) or every RM is prepared (no RM can have acted on an abort).     *)
BTMCommit ==
    /\ btmState = "init"
    /\ tmState = "hidden"
    /\ SomeCommitted \/ AllPrepared
    /\ btmState' = "commit"
    /\ UNCHANGED <<rmState, tmState, tmDecision>>

(* Abort is safe if no RM has committed and some RM aborted or failed.     *)
BTMAbort ==
    /\ btmState = "init"
    /\ tmState = "hidden"
    /\ ~SomeCommitted
    /\ SomeAbortOrFail
    /\ btmState' = "abort"
    /\ UNCHANGED <<rmState, tmState, tmDecision>>

BTMDecide == BTMCommit \/ BTMAbort

-----------------------------------------------------------------------------
Next ==
    \/ \E r \in RM :
          \/ RMPrepare(r)
          \/ RMChooseToAbort(r)
          \/ RMRcvCommit(r)
          \/ RMRcvAbort(r)
          \/ RMFail(r)
    \/ TMCommit
    \/ TMAbort
    \/ TMCrash
    \/ BTMCommit
    \/ BTMAbort

(* Fairness: non-failed RMs, the primary TM (while alive), and the backup *)
(* make progress. Crashes and unilateral aborts are never forced.         *)
Fairness ==
    /\ \A r \in RM : WF_vars(RMProgress(r))
    /\ WF_vars(TMDecide)
    /\ WF_vars(BTMDecide)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* No participant committed while another aborted *)
Consistency ==
    ~ \E r1, r2 \in RM :
        /\ rmState[r1] = "committed"
        /\ rmState[r2] = "aborted"

(* The decision that governs participants: the backup's if it decided, *)
(* otherwise the primary's.                                             *)
EffectiveDecision ==
    IF btmState # "init" THEN btmState ELSE tmDecision

(* All non-failed participants that reached a terminal state agree with *)
(* the effective global decision.                                        *)
DecisionConsistency ==
    /\ \A r \in RM : rmState[r] = "committed" => EffectiveDecision = "commit"
    /\ \A r \in RM :
          (rmState[r] = "aborted" /\ EffectiveDecision # "none")
             => EffectiveDecision = "abort"

(* A commit decision is never produced in a way that violates an abort. *)
CommitValidity ==
    (tmDecision = "commit" \/ btmState = "commit")
        => \A r \in RM : rmState[r] # "aborted"

(* The primary commits only if all participants were prepared. *)
TMCommitValidity ==
    tmState = "commit" => \A r \in RM : rmState[r] \in {"prepared", "committed", "failed"}

(* Failover correctness: the backup acts only after the primary is hidden. *)
BTMOnlyAfterFailover ==
    btmState # "init" => tmState = "hidden"

(* Terminal RM states are irrevocable. *)
TerminalStable ==
    [][\A r \in RM : rmState[r] \in TerminalStates => rmState'[r] = rmState[r]]_vars

(* Decisions are irrevocable. *)
DecisionStable ==
    /\ [][tmDecision # "none" => tmDecision' = tmDecision]_vars
    /\ [][btmState # "init" => btmState' = btmState]_vars

Invariants ==
    /\ TypeOK
    /\ Consistency
    /\ DecisionConsistency
    /\ CommitValidity
    /\ TMCommitValidity
    /\ BTMOnlyAfterFailover

-----------------------------------------------------------------------------
(* Liveness properties *)

AllTerminal == \A r \in RM : rmState[r] \in TerminalStates

Decided == tmDecision # "none" \/ btmState # "init"

(* Every participant eventually reaches a terminal state and the        *)
(* coordinator role (primary or backup) completes the global decision.  *)
Termination == <>[](AllTerminal /\ Decided)

(* If the primary is hidden, the backup eventually decides. *)
BackupCompletes == (tmState = "hidden") ~> (btmState # "init")

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => TerminalStable /\ DecisionStable
THEOREM Spec => Termination /\ BackupCompletes
=============================================================================
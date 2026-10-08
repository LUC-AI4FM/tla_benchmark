-------------------------------- MODULE TwoPhaseCommit --------------------------------
(***************************************************************************)
(* A state-machine model of distributed two-phase commit protocol for a    *)
(* set of participants under asynchronous, nondeterministic execution.     *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS Participants

ASSUME ParticipantsAssumption == Participants # {} /\ IsFiniteSet(Participants)

VARIABLES participantState

(***************************************************************************)
(* The four possible states for each participant:                          *)
(*   - working:   neutral pre-commit state (initial)                       *)
(*   - prepared:  finished local checks, willing to commit                 *)
(*   - committed: decided to commit                                        *)
(*   - aborted:   decided to abort                                         *)
(***************************************************************************)
ParticipantStates == {"working", "prepared", "committed", "aborted"}

TypeOK == participantState \in [Participants -> ParticipantStates]

(***************************************************************************)
(* Global predicates capturing protocol conditions                          *)
(***************************************************************************)

(* True iff all participants have reached the prepared state or beyond *)
AllPreparedOrDecided == 
    \A p \in Participants : participantState[p] \in {"prepared", "committed", "aborted"}

(* True iff all participants are at least prepared (not aborted before preparing) *)
AllPrepared == 
    \A p \in Participants : participantState[p] \in {"prepared", "committed"}

(* True iff at least one participant has decided to commit *)
SomeCommitted == 
    \E p \in Participants : participantState[p] = "committed"

(* True iff at least one participant has decided to abort *)
SomeAborted == 
    \E p \in Participants : participantState[p] = "aborted"

(* True iff at least one participant is still in working state *)
SomeWorking == 
    \E p \in Participants : participantState[p] = "working"

(* True iff some participant will never be able to prepare (already aborted) *)
SomeCannotPrepare == 
    \E p \in Participants : participantState[p] = "aborted"

(* 
   Global condition: committing is allowed only when all participants 
   have prepared and no participant has aborted 
*)
CommitAllowed == AllPrepared /\ ~SomeAborted

(* 
   Global condition: aborting is allowed unless some participant has 
   already committed (in which case we must not abort)
*)
AbortAllowed == ~SomeCommitted

(***************************************************************************)
(* Initial state: all participants begin in working (neutral) state        *)
(***************************************************************************)
Init == participantState = [p \in Participants |-> "working"]

(***************************************************************************)
(* Participant actions as nondeterministic state transitions               *)
(***************************************************************************)

(* 
   Prepare action: A participant in working state may move to prepared 
   state when it has finished local checks and is willing to commit.
   This can happen only if no participant has already aborted.
*)
Prepare(p) ==
    /\ participantState[p] = "working"
    /\ ~SomeAborted  (* Cannot prepare if abort decision already made *)
    /\ participantState' = [participantState EXCEPT ![p] = "prepared"]

(* 
   Decide to commit: A prepared participant may decide to commit only 
   when committing is globally allowed (all prepared, none aborted).
*)
DecideCommit(p) ==
    /\ participantState[p] = "prepared"
    /\ CommitAllowed
    /\ participantState' = [participantState EXCEPT ![p] = "committed"]

(* 
   Decide to abort from prepared state: A prepared participant may 
   decide to abort when aborting is allowed and committing conditions 
   are not met (some participant aborted or not all prepared yet).
*)
DecideAbortFromPrepared(p) ==
    /\ participantState[p] = "prepared"
    /\ AbortAllowed
    /\ (~AllPrepared \/ SomeAborted \/ SomeWorking)
    /\ participantState' = [participantState EXCEPT ![p] = "aborted"]

(* 
   Decide to abort from working state: A participant that has not 
   prepared may decide to abort under appropriate conditions 
   (e.g., timeout, local failure, or learning of another's abort).
*)
DecideAbortFromWorking(p) ==
    /\ participantState[p] = "working"
    /\ AbortAllowed
    /\ participantState' = [participantState EXCEPT ![p] = "aborted"]

(* Combined participant action *)
ParticipantAction(p) ==
    \/ Prepare(p)
    \/ DecideCommit(p)
    \/ DecideAbortFromPrepared(p)
    \/ DecideAbortFromWorking(p)

(***************************************************************************)
(* Next state relation: nondeterministic interleaving of participant       *)
(* actions                                                                 *)
(***************************************************************************)
Next == \E p \in Participants : ParticipantAction(p)

(***************************************************************************)
(* Fairness: Weak fairness on each participant's actions ensures progress  *)
(***************************************************************************)
Fairness == \A p \in Participants : WF_participantState(ParticipantAction(p))

(***************************************************************************)
(* Complete specification with fairness                                     *)
(***************************************************************************)
Spec == Init /\ [][Next]_participantState /\ Fairness

(***************************************************************************)
(* SAFETY INVARIANTS                                                       *)
(***************************************************************************)

(*
   Agreement (Consistency): No two participants can end up with 
   conflicting final decisions - one committed and another aborted.
*)
Agreement == ~(SomeCommitted /\ SomeAborted)

(*
   Type safety combined with agreement
*)
SafetyInvariant == TypeOK /\ Agreement

(***************************************************************************)
(* LIVENESS-STYLE SAFETY CONDITION                                         *)
(***************************************************************************)

(*
   Commit possibility: When all participants are prepared (and none 
   aborted), at least one participant can take a commit action.
   This ensures no global deadlock preventing commit decisions when 
   everyone is prepared.
*)
CommitPossibleWhenAllPrepared ==
    (AllPrepared /\ ~SomeAborted) => 
        \E p \in Participants : 
            /\ participantState[p] = "prepared"
            /\ ENABLED DecideCommit(p)

(*
   Alternative formulation: if all are prepared and none committed/aborted,
   the system is not deadlocked with respect to commit decisions.
*)
NoDeadlockWhenAllPrepared ==
    (\A p \in Participants : participantState[p] = "prepared") =>
        \E p \in Participants : ENABLED DecideCommit(p)

(***************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(***************************************************************************)

(*
   Termination: Every participant eventually reaches a final decision 
   (committed or aborted).
*)
AllDecided == \A p \in Participants : participantState[p] \in {"committed", "aborted"}

EventuallyAllDecide == <>AllDecided

(*
   If all prepare, then all eventually commit.
*)
AllCommitted == \A p \in Participants : participantState[p] = "committed"

PrepareLeadsToCommit ==
    []((AllPrepared /\ ~SomeAborted) => <>AllCommitted)

(***************************************************************************)
(* THEOREMS (Properties to verify)                                          *)
(***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => []SafetyInvariant
THEOREM Spec => EventuallyAllDecide

===================================================================================
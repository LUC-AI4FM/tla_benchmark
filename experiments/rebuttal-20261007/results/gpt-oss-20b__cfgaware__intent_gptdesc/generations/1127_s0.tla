MODULE TwoPhaseCommit
EXTENDS Naturals, TLC

CONSTANTS RM          \* Set of resource managers (participants)

VARIABLE r2           \* Mapping from each participant to its current state

(* --------------------------------------------------------------------------- *)
(* States that a participant may occupy *)
State == {"Neutral", "Prepared", "Committed", "Aborted"}

(* --------------------------------------------------------------------------- *)
(* Initial condition: every participant starts in the neutral pre‑commit state *)
Init == \A r \in RM : r2[r] = "Neutral"

(* Helper predicate: all participants are prepared *)
AllPrepared == \A r \in RM : r2[r] = "Prepared"

(* --------------------------------------------------------------------------- *)
(* Actions for a single participant *)

Prepare(r) ==
  /\ r2[r] = "Neutral"
  /\ r2' = [r2 EXCEPT ![r] = "Prepared"]

Commit(r) ==
  /\ r2[r] = "Prepared"
  /\ AllPrepared
  /\ r2' = [r2 EXCEPT ![r] = "Committed"]

Abort(r) ==
  /\ r2[r] \in {"Neutral", "Prepared"}
  /\ r2' = [r2 EXCEPT ![r] = "Aborted"]

(* --------------------------------------------------------------------------- *)
(* Non‑deterministic interleaving of participant actions *)
Next == \E r \in RM : Prepare(r) \/ Commit(r) \/ Abort(r)

(* --------------------------------------------------------------------------- *)
(* Specification: initial condition, next‑state relation,
   and a liveness‑style safety requirement that commit is possible
   when all participants are prepared. *)
TCSpec ==
  Init
  /\ [][Next]_r2
  /\ [] (AllPrepared => <> (\A r \in RM : r2[r] = "Committed"))

(* --------------------------------------------------------------------------- *)
(* Invariants *)

(* Type safety: every participant state is one of the four intended states *)
TCTypeOK == \A r \in RM : r2[r] \in State

(* Agreement (consistency): no two participants can end up with conflicting
   final decisions (one committed and another aborted). *)
TCConsistent ==
  \A r1, r2' \in RM :
    ~(r2[r1] = "Committed" /\ r2[r2'] = "Aborted")

=============================================================================
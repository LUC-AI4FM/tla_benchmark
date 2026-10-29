------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Two-Phase Commit: abstract specification of the resource managers (RMs) *)
(* only. There is no coordinator, no message passing, and no faults beyond *)
(* the commit/abort logic.                                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

States == {"working", "prepared", "committed", "aborted"}

-----------------------------------------------------------------------------
(* Type-correctness invariant *)
TCTypeOK == rmState \in [RM -> States]

(* Initial predicate: every RM starts in the "working" state *)
TCInit == rmState = [r \in RM |-> "working"]

(* True iff all RMs are prepared or committed, so committing is possible *)
canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

(* True iff no RM has committed, so aborting is still possible *)
notCommitted == \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
(* Actions *)

(* RM r moves from working to prepared *)
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

(* RM r decides to commit or abort *)
Decide(r) ==
    \/ /\ rmState[r] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    \/ /\ rmState[r] \in {"working", "prepared"}
       /\ notCommitted
       /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

(* Next-state relation: the disjunction of the actions of all RMs *)
TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

-----------------------------------------------------------------------------
(* Consistency invariant: no RM has aborted while another has committed *)
TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

(* Complete specification *)
TCSpec == TCInit /\ [][TCNext]_vars

(* Standard names *)
Init == TCInit
Next == TCNext
Spec == TCSpec

TypeOK      == TCTypeOK
Consistency == TCConsistent

-----------------------------------------------------------------------------
(* Properties asserted for the protocol *)
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================
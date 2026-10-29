------------------------------- MODULE Session1 -------------------------------
(***************************************************************************)
(* Session1: a foundational system model intended to be extended by a     *)
(* separate model-checking module (e.g. MC_Session1). It is a small       *)
(* bounded cyclic counter with an explicit control phase.                  *)
(*                                                                         *)
(* The counter starts at 0 in phase "counting". While counting, it         *)
(* increments by one until it reaches the bound N. When it reaches N, the  *)
(* system switches to phase "resetting". It then resets the counter to 0   *)
(* and returns to "counting". The cycle repeats forever.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N            \* Upper bound of the counter

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES count,      \* Current counter value
          phase       \* Control phase: "counting" or "resetting"

vars == <<count, phase>>

Phases == {"counting", "resetting"}

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ count \in 0..N
    /\ phase \in Phases

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ count = 0
    /\ phase = "counting"

-----------------------------------------------------------------------------
(* Actions *)

\* Increment the counter while it is below the bound.
Increment ==
    /\ phase = "counting"
    /\ count < N
    /\ count' = count + 1
    /\ phase' = IF count + 1 = N THEN "resetting" ELSE "counting"

\* Reset the counter once it has reached the bound.
Reset ==
    /\ phase = "resetting"
    /\ count = N
    /\ count' = 0
    /\ phase' = "counting"

Next ==
    \/ Increment
    \/ Reset

-----------------------------------------------------------------------------
(* Specification with weak fairness to guarantee progress *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

\* The counter never exceeds its bound.
BoundedCount == count <= N

\* The phase is consistent with the counter value.
PhaseConsistency ==
    /\ (phase = "resetting") => (count = N)
    /\ (phase = "counting")  => (count < N)

\* Every step either increments by exactly one or resets from N to 0.
StepProperty ==
    [][ \/ count' = count + 1
        \/ (count = N /\ count' = 0) ]_vars

Safety ==
    /\ TypeOK
    /\ BoundedCount
    /\ PhaseConsistency

-----------------------------------------------------------------------------
(* Liveness properties *)

\* The counter reaches its bound infinitely often.
ReachesBound == []<>(count = N)

\* The counter returns to zero infinitely often.
ReturnsToZero == []<>(count = 0)

\* Whenever the system is resetting, it eventually resumes counting.
ResetLeadsToCounting == (phase = "resetting") ~> (phase = "counting")

Liveness ==
    /\ ReachesBound
    /\ ReturnsToZero
    /\ ResetLeadsToCounting

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => StepProperty
THEOREM Spec => Liveness

=============================================================================
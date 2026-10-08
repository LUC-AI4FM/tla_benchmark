------------------------------ MODULE StateConstraintLivenessPitfall ------------------------------

EXTENDS TLC, Sequences

CONSTANT MaxLogLen

VARIABLES phase, hist

(*
  This module illustrates a pitfall: adding a state constraint for TLC model checking
  can spuriously make a liveness property appear to hold. The system alternates forever
  between A and B (never reaches "Done"). A state constraint limits the history length,
  which can cut off all infinite behaviors that witness the liveness violation.
*)

vars == << phase, hist >>

Init ==
  /\ phase = "A"
  /\ hist = << phase >>

AtoB ==
  /\ phase = "A"
  /\ phase' = "B"
  /\ hist' = Append(hist, phase')

BtoA ==
  /\ phase = "B"
  /\ phase' = "A"
  /\ hist' = Append(hist, phase')

Next == AtoB \/ BtoA

(*
  Weak fairness ensures the system keeps making progress (no infinite stuttering)
  as long as Next remains enabled. Since Next is always enabled in the unconstrained
  system, behaviors alternate A,B,A,B,....
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
  State constraint for TLC: bound the length of the history log.
  In TLC, set CONSTRAINT StateConstraint in the model.
*)
StateConstraint == Len(hist) <= MaxLogLen

(*
  The liveness claim we want to check. It is actually false for the unconstrained system
  because "Done" is never reached; the system only alternates between "A" and "B".
  With the state constraint active, TLC can spuriously report this as satisfied,
  because the constraint prunes all infinite behaviors that would violate it.
*)
EventuallyDone == <> (phase = "Done")

(*
  Optional sanity invariant.
*)
TypeInvariant ==
  /\ phase \in {"A", "B"}
  /\ hist \in Seq({"A", "B"})

==============================================================
---- MODULE StateConstraintPitfall ----
EXTENDS Naturals, Sequences

(*
This specification illustrates a pitfall when using TLC state constraints together with liveness:
- The system toggles forever between states "A" and "B".
- Weak fairness on the Toggle action ensures perpetual progress in the unconstrained system.
- A liveness property claims the system eventually reaches "Done", which is false.
- Introducing a TLC State Constraint that bounds the history length (StateConstraint) can spuriously
  make the liveness property appear satisfied because the constraint prunes all infinite behaviors.

To reproduce the pitfall in TLC:
- Use Spec as the temporal specification.
- Add EventuallyDone as a liveness property to check.
- Set State Constraint to: StateConstraint
- Provide a small positive value for MaxLen (e.g., 5).
*)

CONSTANT MaxLen
ASSUME MaxLen \in Nat \ {0}

VARIABLES pc, hist

vars == << pc, hist >>

States == {"A", "B", "Done"}
AB == {"A", "B"}

Init ==
  /\ pc = "A"
  /\ hist = << "A" >>

Toggle ==
  /\ pc \in AB
  /\ pc' = IF pc = "A" THEN "B" ELSE "A"
  /\ hist' = Append(hist, pc')

Next == Toggle

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Toggle)

(*
Safety invariants to check with TLC (as invariants):
- TypeInv: variable typing
- AlwaysABOnly: the system never reaches "Done" (captures the true safety fact of the unconstrained spec)
*)
TypeInv ==
  /\ pc \in States
  /\ hist \in Seq(States)

AlwaysABOnly == [](pc \in AB)

(*
Liveness property to check with TLC:
This should FAIL without the state constraint (the system never reaches "Done"),
but may appear to PASS if TLC applies the StateConstraint below.
*)
EventuallyDone == <> (pc = "Done")

(*
TLC State Constraint (to be added in the model, not conjoined to Spec):
Bounding the history length prunes all runs after at most MaxLen-1 steps.
This can eliminate the infinite counterexample to EventuallyDone.
*)
StateConstraint == Len(hist) < MaxLen

====
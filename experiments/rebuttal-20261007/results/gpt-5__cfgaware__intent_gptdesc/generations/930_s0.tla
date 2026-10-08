----------------------------- MODULE TwelveHourClock -----------------------------
EXTENDS Naturals

(*
  A concise discrete-time model of a 12-hour cyclic clock.
  State: single variable h in 1..12.
  Step: increment by one hour, wrapping 12 -> 1.
*)

VARIABLE h

NextVal(x) == IF x # 12 THEN x + 1 ELSE 1

(*
  Initial condition: hour is a valid 12-hour value.
*)
HCini == h \in 1..12

(*
  Transition relation: deterministic modulo-12 increment.
*)
HC == h' = NextVal(h)

(*
  Full behavior with strong fairness: ongoing clock under fair execution.
*)
Spec == HCini /\ [][HC]_h /\ SF_h(HC)

(*
  Invariants and properties to be checked.
*)

(* Safety invariant: hour always remains within 1..12. *)
TypeInv == h \in 1..12

(* Each transition preserves the invariant (state-action invariant). *)
StepPreservesType == TypeInv /\ HC => TypeInv'

(* Functional correctness: the step relation implements the modulo-12 increment. *)
Modulo12Step == HC <=> (h' = NextVal(h))

(* Liveness: under fair execution, every hour value recurs infinitely often. *)
CycleLiveness == \A i \in 1..12 : []<>(h = i)

(* Initialization implies the invariant holds globally under the specification. *)
InitImpliesInvariant == Spec => []TypeInv

(* Under fair execution, the clock cycles through all 12 values infinitely often. *)
FairCycles == Spec => CycleLiveness
===============================================================================
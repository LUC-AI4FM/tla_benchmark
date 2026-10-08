----------------------------- MODULE SimpleState -----------------------------
EXTENDS Integers, FiniteSets

(*
A simple state holding one integer value selected from a fixed finite set.
Initialization nondeterministically picks any allowed value that also
satisfies a numeric predicate (NumPred) and an additional boolean
requirement (BoolReq). No further state updates occur.
*)

CONSTANTS
  Allowed,   \* a fixed finite set of integers that may be chosen
  Threshold, \* an integer used by the numeric predicate
  Good       \* a subset indicating where the additional boolean requirement holds

(*
Basic assumptions about constants.
*)
ASSUME /\ Allowed \subseteq Int
       /\ IsFiniteSet(Allowed)
ASSUME Good \subseteq Allowed
ASSUME Threshold \in Int

(*
Predicates made explicit.
- AllowedVal(v): v is in the allowed universe.
- NumPred(v): numeric predicate (here: v > Threshold).
- BoolReq(v): additional boolean requirement (here: v \in Good).
*)
AllowedVal(v) == v \in Allowed
NumPred(v)    == v > Threshold
BoolReq(v)    == v \in Good

VARIABLE val

Init ==
  /\ AllowedVal(val)
  /\ NumPred(val)
  /\ BoolReq(val)

Next ==
  UNCHANGED val

vars == << val >>

Spec == Init /\ [][Next]_vars

(*
Safety invariant: every reachable state satisfies all requirements.
*)
Inv == AllowedVal(val) /\ NumPred(val) /\ BoolReq(val)

THEOREM Spec => []Inv

(*
Optional satisfiability assertion: there exists at least one initial value.
*)
NumOKSet == { x \in Int : NumPred(x) }
InitSatisfiable == (Allowed \cap Good \cap NumOKSet) # {}
ASSUME InitSatisfiable
============================================================================
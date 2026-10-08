----------------------------- MODULE SingleValueState -----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    ALLOWED,     \* A fixed finite set of integers
    Threshold,   \* Numeric threshold
    Attr         \* A Boolean attribute function over ALLOWED

VARIABLES
    v            \* The single stored value

(*
  Numeric predicate: value must be greater than Threshold.
*)
NumPred(x) == x > Threshold

(*
  Boolean requirement: Attr[x] must hold for the chosen value.
  Defined safely for all x by guarding with DOMAIN Attr.
*)
BoolReq(x) == IF x \in DOMAIN Attr THEN Attr[x] ELSE FALSE

(*
  The set of allowed initial values that satisfy both constraints.
*)
GoodSet == { x \in ALLOWED : NumPred(x) /\ BoolReq(x) }

(*
  Basic assumptions about constants:
  - ALLOWED is a finite subset of Int
  - Attr is a total Boolean function over ALLOWED
  - The initialization predicate is satisfiable (at least one valid value exists)
*)
ASSUME
  /\ ALLOWED \subseteq Int
  /\ IsFiniteSet(ALLOWED)
  /\ Attr \in [ALLOWED -> BOOLEAN]
  /\ GoodSet # {}

Init ==
  \* Nondeterministically choose any valid initial value.
  v \in GoodSet

Next ==
  \* No state updates after initialization.
  UNCHANGED v

Spec ==
  Init /\ [][Next]_v

(*
  Safety invariants: every reachable state keeps v within the allowed universe
  and satisfying both the numeric and Boolean predicates.
*)
TypeInv == v \in ALLOWED
NumInv  == NumPred(v)
BoolInv == BoolReq(v)
Inv     == TypeInv /\ NumInv /\ BoolInv

Safety == []Inv

(*
  Trivial liveness: once initialized, the value persists forever (no changes).
*)
Persistence == [](UNCHANGED v)

=============================================================================
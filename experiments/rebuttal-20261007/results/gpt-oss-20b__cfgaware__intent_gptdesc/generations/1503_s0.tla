------------------------------ MODULE SimpleState ------------------------------
EXTENDS Naturals

CONSTANTS
    Universe,          \* Finite set of integers that may be chosen
    Threshold          \* Numeric threshold used in the predicate

VARIABLE v            \* The single state value

(* ------------------------------------------------------------------------- *)
(*  Predicates and allowed values                                            *)
(* ------------------------------------------------------------------------- *)

Pred(x) == x > Threshold

BoolCond(x) == (x % 2 = 0)

AllowedValues == {x \in Universe : Pred(x) /\ BoolCond(x)}

(* ------------------------------------------------------------------------- *)
(*  Initialisation and transition relation                                   *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ v \in AllowedValues

Next ==
    /\ v' = v

(* ------------------------------------------------------------------------- *)
(*  Invariant (safety property)                                              *)
(* ------------------------------------------------------------------------- *)

Safety ==
    /\ v \in Universe
    /\ Pred(v)
    /\ BoolCond(v)

(* ------------------------------------------------------------------------- *)
(*  Existence of at least one admissible value                               *)
(* ------------------------------------------------------------------------- *)

THEOREM ExistsAllowedValue ==
    EXISTS x \in Universe : Pred(x) /\ BoolCond(x)

=============================================================================
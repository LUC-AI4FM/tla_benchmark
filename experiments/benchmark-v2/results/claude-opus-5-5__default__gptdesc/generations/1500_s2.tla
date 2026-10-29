---------------------------- MODULE CoverageStatistics ----------------------------
(***************************************************************************)
(* A small specification used to exercise coverage statistics for         *)
(* different syntactic forms of actions and UNCHANGED expressions.  The   *)
(* purpose is to test how coverage reporting treats aliases, tuples, and  *)
(* the various UNCHANGED forms, not to model a realistic algorithm.       *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

(* Aliases for the state variables *)
a == x
b == y

(* Tuple aliases *)
ab == <<a, b>>
xy == <<x, y>>

Init ==
    /\ x = 0
    /\ y = 0

(* Modify x, leave y unchanged via plain UNCHANGED *)
A1 ==
    /\ x' = x + 1
    /\ UNCHANGED y

(* Modify y, leave x unchanged via an alias *)
A2 ==
    /\ y' = y + 1
    /\ UNCHANGED a

(* Leave both unchanged using a tuple of variables *)
A3 ==
    /\ x < 10
    /\ UNCHANGED <<x, y>>

(* Leave both unchanged using the vars tuple *)
A4 ==
    /\ y < 10
    /\ UNCHANGED vars

(* Leave both unchanged using a tuple of aliases *)
A5 ==
    /\ UNCHANGED <<a, b>>

(* Leave both unchanged using an aliased tuple *)
A6 ==
    /\ UNCHANGED ab

(* Leave both unchanged using a nested tuple *)
A7 ==
    /\ UNCHANGED <<xy, <<a>>, b>>

(* Explicit primed equalities instead of UNCHANGED *)
A8 ==
    /\ x' = x
    /\ y' = y

(* Modify both variables *)
A9 ==
    /\ x' = x + 1
    /\ y' = x

(* Modify y, leave x unchanged via a single-element tuple *)
A10 ==
    /\ y' = y + 2
    /\ UNCHANGED <<x>>

Next ==
    \/ A1
    \/ A2
    \/ A3
    \/ A4
    \/ A5
    \/ A6
    \/ A7
    \/ A8
    \/ A9
    \/ A10

Spec == Init /\ [][Next]_vars

(* State constraint intended for model checking *)
Constraint == x < 20

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

===============================================================================
--------------------------- MODULE InitStateTest ---------------------------
(***************************************************************************)
(* A test specification exploring how TLC generates initial states from   *)
(* differently structured formulas.  The single variable x is assigned by *)
(* one of several sub-predicates of Init.                                  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE x

(* x = 0, with a tautological disjunction as the second conjunct. *)
I1a == /\ x = 0
       /\ \/ TRUE
          \/ TRUE

(* x = 1, with a tautological disjunction placed first.  TLC explores *)
(* both disjuncts and generates the state x = 1 twice.                *)
I1b == /\ \/ TRUE
          \/ TRUE
       /\ x = 1

(* x = 2.  The double negation stops TLC from splitting the disjunction *)
(* into separate branches, so no duplicate state is generated.          *)
I1c == /\ ~~(\/ TRUE
             \/ TRUE)
       /\ x = 2

(* A false conjunct before the assignment, so it never succeeds. *)
I2 == /\ FALSE
      /\ x = 3

(* A false conjunct after the assignment, so it never succeeds. *)
I3 == /\ x = 4
      /\ FALSE

(* x = 5 or x = 6, through nested disjunctions. *)
I4 == \/ x = 5
      \/ \/ FALSE
         \/ x = 6

(* A plain assignment. *)
I5 == x = 7

Init == \/ I1a
        \/ I1b
        \/ I1c
        \/ I2
        \/ I3
        \/ I4
        \/ I5

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
=============================================================================
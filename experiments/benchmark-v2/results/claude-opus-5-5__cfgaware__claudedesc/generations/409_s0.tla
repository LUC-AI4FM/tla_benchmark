---- MODULE SetOfFcns ----
EXTENDS Naturals, TLC

(***************************************************************************)
(* Performance test for TLC's handling of large sets of functions.         *)
(*                                                                         *)
(* The single variable x is initially any function from {1,...,6} to      *)
(* {1,...,7}, giving 7^6 = 117649 distinct initial states.  The next-state *)
(* relation leaves x unchanged, so the test measures TLC's ability to      *)
(* enumerate and store a large number of initial states.                   *)
(*                                                                         *)
(* Empirical results (recorded):                                           *)
(*   - 7^6 = 117649 states: completed, roughly 1,200-1,500 states/second. *)
(*   - 6^7 = 279936 states: completed, roughly 1,200-1,500 states/second. *)
(*   - 7^7 = 823543 states: exceeded available resources on some machines.*)
(***************************************************************************)

VARIABLE x

Init == /\ PrintT("Should find 7^6 = 117649 states")
        /\ x \in [{1, 2, 3, 4, 5, 6} -> {1, 2, 3, 4, 5, 6, 7}]

Next == UNCHANGED x

Inv == TRUE

====
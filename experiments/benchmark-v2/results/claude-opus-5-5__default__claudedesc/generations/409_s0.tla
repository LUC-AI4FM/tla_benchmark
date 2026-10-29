---------------------------- MODULE SetOfFcnsPerf ----------------------------
(***************************************************************************)
(* Performance test for TLC's handling of large sets of functions.         *)
(*                                                                         *)
(* The variable x is initialized to any function from {1,...,6} to        *)
(* {1,...,7}, giving 7^6 = 117,649 distinct initial states.  The next-     *)
(* state relation leaves x unchanged, so the test measures TLC's ability   *)
(* to enumerate and store a large number of initial states.                *)
(*                                                                         *)
(* Empirical results (recorded on various machines):                       *)
(*   - State generation rates of roughly 1,200 - 1,500 states per second.  *)
(*   - 7^6 (117,649 states) completes successfully.                        *)
(*   - 6^7 (279,936 states) completes successfully.                        *)
(*   - 7^7 (823,543 states) exceeds available resources on some machines.  *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLE x

vars == << x >>

Domain   == {1, 2, 3, 4, 5, 6}
Codomain == {1, 2, 3, 4, 5, 6, 7}

TypeOK == x \in [Domain -> Codomain]

Init == /\ Print("Should find 7^6 = 117649 distinct states", TRUE)
        /\ x \in [Domain -> Codomain]

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(* Trivially true invariant; a placeholder required by the configuration. *)
Inv == TRUE

=============================================================================
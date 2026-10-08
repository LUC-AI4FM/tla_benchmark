------------------------------ MODULE EuclidGCD ------------------------------
EXTENDS Naturals

CONSTANTS X0, YRange \* X0 is the fixed value (24), YRange ⊆ 1..50

VARIABLES x, y, done

(* ------------------------------------------------------------------------- *)
(* Initial state: one variable is fixed at X0, the other nondeterministically
   chosen from YRange. The algorithm has not yet terminated.                 *)
Init ==
    /\ x = X0
    /\ y \in YRange
    /\ done = FALSE

(* ------------------------------------------------------------------------- *)
(* One step of Euclid's subtraction-based GCD algorithm.                     *)
Step ==
    IF x > 0 THEN
        IF x < y THEN
            LET temp == x IN
                /\ x' = temp - y
                /\ y' = temp
        ELSE
            /\ x' = x - y
            /\ y' = y
        /\ done' = FALSE
    ELSE
        /\ done' = TRUE

(* ------------------------------------------------------------------------- *)
(* The next-state relation.                                                  *)
Next == Step

(* ------------------------------------------------------------------------- *)
(* Complete specification: initial state followed by arbitrary many steps.   *)
Spec == Init /\ [][Next]_<<x, y, done>>

(* ------------------------------------------------------------------------- *)
(* Optional theorem stating that the algorithm eventually reaches a done
   state.  This is not required for termination checking but illustrates
   liveness.                                                              *)
THEOREM Termination ==
    Spec => <> (done)

=============================================================================
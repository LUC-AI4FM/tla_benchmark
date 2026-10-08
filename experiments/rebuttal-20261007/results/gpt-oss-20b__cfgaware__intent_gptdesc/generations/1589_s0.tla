------------------------------ MODULE EuclidGCD ------------------------------
EXTENDS Integers

CONSTANT MaxVal \in Nat

VARIABLES x, y, origX, origY

(* ------------------------------------------------------------------ *)
(* GCD function: Euclidean algorithm using modulo. *)
GCD(a,b) == IF b = 0 THEN a ELSE GCD(b, a MOD b)

(* ------------------------------------------------------------------ *)
(* Initial state: two arbitrary positive integers within bound. *)
Init ==
    /\ x \in 1..MaxVal
    /\ y \in 1..MaxVal
    /\ origX = x
    /\ origY = y

(* ------------------------------------------------------------------ *)
(* Next-state relation: subtraction-based Euclidean algorithm. *)
Next ==
    \/ /\ x > y
       /\ x' = x - y
       /\ y' = y
    \/ /\ y > x
       /\ y' = y - x
       /\ x' = x
    \/ /\ x = y
       /\ x' = 0
       /\ y' = x

(* ------------------------------------------------------------------ *)
Spec == Init /\ [] (Next)

(* ------------------------------------------------------------------ *)
Termination == <> (x = 0 \/ y = 0)

(* ------------------------------------------------------------------ *)
Invariant ==
    /\ x \in Nat
    /\ y \in Nat
    /\ GCD(x,y) = GCD(origX, origY)
    /\ (x > 0 \/ y > 0)

=============================================================================
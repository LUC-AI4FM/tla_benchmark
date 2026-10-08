---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES x, y, done, original_y

vars == <<x, y, done, original_y>>

-----------------------------------------------------------------------------
(* Mathematical GCD operator using recursive definition *)
RECURSIVE GCD(_, _)
GCD(a, b) == IF b = 0 THEN a
             ELSE IF a = 0 THEN b
             ELSE IF a > b THEN GCD(a - b, b)
             ELSE GCD(a, b - a)

-----------------------------------------------------------------------------
(* Initial state: x is 24, y is nondeterministically chosen from 1..N *)
Init == 
    /\ x = 24
    /\ y \in 1..N
    /\ original_y = y
    /\ done = FALSE

-----------------------------------------------------------------------------
(* Subtraction step: subtract smaller from larger *)
Subtract ==
    /\ ~done
    /\ x > 0
    /\ y > 0
    /\ IF x > y 
       THEN /\ x' = x - y
            /\ y' = y
       ELSE /\ y' = y - x
            /\ x' = x
    /\ done' = done
    /\ original_y' = original_y

(* Finish step: when one value reaches zero, print result and mark done *)
Finish ==
    /\ ~done
    /\ (x = 0 \/ y = 0)
    /\ done' = TRUE
    /\ PrintT(<<"GCD of 24 and", original_y, "is", IF x = 0 THEN y ELSE x>>)
    /\ UNCHANGED <<x, y, original_y>>

-----------------------------------------------------------------------------
(* Next state relation *)
Next == Subtract \/ Finish

(* Fairness condition to ensure progress *)
Fairness == WF_vars(Next)

(* Complete specification with fairness *)
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Termination property: eventually done becomes TRUE *)
Termination == <>done

-----------------------------------------------------------------------------
(* Invariant: the GCD of current values equals GCD of original values *)
GCDInvariant == 
    ~done => GCD(x, y) = GCD(24, original_y)

(* Correctness: when done, the result is the true GCD *)
Correctness ==
    done => (IF x = 0 THEN y ELSE x) = GCD(24, original_y)

-----------------------------------------------------------------------------
(* Type invariant for safety checking *)
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat
    /\ done \in BOOLEAN
    /\ original_y \in 1..N

=============================================================================
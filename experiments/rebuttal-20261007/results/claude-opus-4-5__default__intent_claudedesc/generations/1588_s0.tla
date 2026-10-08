---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, TLC

CONSTANTS N

VARIABLES x, y, x0, y0, done, printed

vars == <<x, y, x0, y0, done, printed>>

ASSUME N \in Nat /\ N >= 1

(* Mathematical GCD operator using recursion *)
RECURSIVE MathGCD(_, _)
MathGCD(a, b) == 
    IF b = 0 THEN a
    ELSE MathGCD(b, a % b)

(* Initialize: x = 24, y is nondeterministically chosen from 1..N *)
Init ==
    /\ x0 = 24
    /\ x = 24
    /\ y0 \in 1..N
    /\ y = y0
    /\ done = FALSE
    /\ printed = FALSE

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
    /\ UNCHANGED <<x0, y0, done, printed>>

(* Check if algorithm is finished (one value reached zero) *)
Finish ==
    /\ ~done
    /\ (x = 0 \/ y = 0)
    /\ done' = TRUE
    /\ UNCHANGED <<x, y, x0, y0, printed>>

(* Print result after finishing *)
PrintResult ==
    /\ done
    /\ ~printed
    /\ PrintT(<<"GCD of", x0, "and", y0, "is", IF x = 0 THEN y ELSE x>>)
    /\ printed' = TRUE
    /\ UNCHANGED <<x, y, x0, y0, done>>

(* Next state relation *)
Next == Subtract \/ Finish \/ PrintResult

(* Fairness: weak fairness on all actions to ensure progress *)
Fairness == 
    /\ WF_vars(Subtract)
    /\ WF_vars(Finish)
    /\ WF_vars(PrintResult)

(* Specification with fairness *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* The result when done *)
Result == IF x = 0 THEN y ELSE x

(* Safety invariant: values stay non-negative *)
TypeInvariant ==
    /\ x \in Nat
    /\ y \in Nat
    /\ x0 = 24
    /\ y0 \in 1..N
    /\ done \in BOOLEAN
    /\ printed \in BOOLEAN

(* Safety invariant: GCD is preserved throughout computation *)
GCDPreserved ==
    ~done => MathGCD(x, y) = MathGCD(x0, y0)

(* Safety invariant: when done, the result equals the mathematical GCD *)
CorrectResult ==
    done => Result = MathGCD(x0, y0)

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeInvariant
    /\ GCDPreserved
    /\ CorrectResult

(* Termination property: the algorithm eventually finishes and prints *)
Termination == <>(done /\ printed)

==========================================================================
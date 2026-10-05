---------------------------- MODULE EuclidGCD ----------------------------

EXTENDS Integers, Naturals, FiniteSets

CONSTANTS M, N_Max

ASSUME M \in Nat /\ M > 0
ASSUME N_Max \in Nat /\ N_Max > 0

VARIABLES x, y, x0, y0, pc

vars == <<x, y, x0, y0, pc>>

\* Recursive GCD definition for specification purposes
RECURSIVE GCD(_, _)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat
    /\ x0 \in Nat
    /\ y0 \in Nat
    /\ pc \in {"loop", "done"}

Init ==
    /\ x = M
    /\ y \in 1..N_Max
    /\ x0 = x
    /\ y0 = y
    /\ pc = "loop"

\* The loop step: if both x and y are positive, subtract smaller from larger
Loop ==
    /\ pc = "loop"
    /\ x > 0
    /\ y > 0
    /\ IF x >= y
       THEN x' = x - y /\ y' = y
       ELSE x' = x /\ y' = y - x
    /\ x0' = x0
    /\ y0' = y0
    /\ pc' = "loop"

\* Termination: when one of x or y becomes zero
Terminate ==
    /\ pc = "loop"
    /\ (x = 0 \/ y = 0)
    /\ pc' = "done"
    /\ UNCHANGED <<x, y, x0, y0>>

\* Stuttering when already done
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop) /\ WF_vars(Terminate)

\* ----- Safety Invariants -----

\* Both values remain nonnegative
NonNegative == x >= 0 /\ y >= 0

\* Values stay within initial bounds
Bounded == x <= x0 + y0 /\ y <= x0 + y0

\* GCD is preserved throughout computation
GCDPreserved == GCD(x, y) = GCD(x0, y0)

\* When terminated, the nonzero value equals the GCD of initial inputs
CorrectResult ==
    pc = "done" => 
        (x = 0 /\ y = GCD(x0, y0)) \/ (y = 0 /\ x = GCD(x0, y0))

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ NonNegative
    /\ Bounded
    /\ GCDPreserved
    /\ CorrectResult

\* ----- Liveness Properties -----

\* The algorithm eventually terminates
Termination == <>(pc = "done")

\* Eventually one of the values becomes zero
EventuallyZero == <>(x = 0 \/ y = 0)

==========================================================================
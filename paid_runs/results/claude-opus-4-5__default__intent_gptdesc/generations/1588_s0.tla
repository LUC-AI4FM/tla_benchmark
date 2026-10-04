-------------------------------- MODULE GCD --------------------------------

EXTENDS Naturals, TLAPS

CONSTANTS A, N

ASSUME APositive == A \in Nat \ {0}
ASSUME NPositive == N \in Nat \ {0}

VARIABLES x, y, b0, done

vars == <<x, y, b0, done>>

-----------------------------------------------------------------------------

RECURSIVE GCD_func(_, _)
GCD_func(m, n) ==
    IF n = 0 THEN m
    ELSE IF m = 0 THEN n
    ELSE IF m > n THEN GCD_func(m - n, n)
    ELSE GCD_func(m, n - m)

-----------------------------------------------------------------------------

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat
    /\ b0 \in 1..N
    /\ done \in BOOLEAN

BoundsInvariant ==
    /\ x <= A + N
    /\ y <= A + N
    /\ (done = FALSE) => (x > 0 \/ y > 0)

GCDPreserved ==
    GCD_func(x, y) = GCD_func(A, b0)

SafetyInvariant ==
    /\ TypeOK
    /\ BoundsInvariant
    /\ GCDPreserved

-----------------------------------------------------------------------------

Init ==
    /\ x = A
    /\ y \in 1..N
    /\ b0 = y
    /\ done = FALSE

-----------------------------------------------------------------------------

Swap ==
    /\ done = FALSE
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ b0' = b0
    /\ done' = FALSE

SubtractYFromX ==
    /\ done = FALSE
    /\ x >= y
    /\ y > 0
    /\ x' = x - y
    /\ y' = y
    /\ b0' = b0
    /\ done' = (x - y = 0)

SubtractXFromY ==
    /\ done = FALSE
    /\ y > x
    /\ x > 0
    /\ y' = y - x
    /\ x' = x
    /\ b0' = b0
    /\ done' = (y - x = 0)

Terminate ==
    /\ done = FALSE
    /\ (x = 0 \/ y = 0)
    /\ done' = TRUE
    /\ x' = x
    /\ y' = y
    /\ b0' = b0

Step == Swap \/ SubtractYFromX \/ SubtractXFromY \/ Terminate

Stutter ==
    /\ done = TRUE
    /\ UNCHANGED vars

Next == Step \/ Stutter

-----------------------------------------------------------------------------

Fairness == WF_vars(Step)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

Halted == done = TRUE

CorrectnessAtTermination ==
    done = TRUE => 
        \/ (x = 0 /\ y = GCD_func(A, b0))
        \/ (y = 0 /\ x = GCD_func(A, b0))

Termination == <>Halted

LivenessProperty == <>(done = TRUE /\ CorrectnessAtTermination)

Safety ==
    /\ TypeOK
    /\ GCDPreserved
    /\ (done = FALSE /\ x > 0 /\ y > 0) => (x > 0 /\ y > 0)

Invariant == SafetyInvariant /\ CorrectnessAtTermination

=============================================================================
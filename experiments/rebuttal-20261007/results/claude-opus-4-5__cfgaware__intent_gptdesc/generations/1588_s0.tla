---------------------------- MODULE GCD ----------------------------
EXTENDS Integers, Naturals

CONSTANTS A, N

VARIABLES x, y, b0, done

vars == <<x, y, b0, done>>

-----------------------------------------------------------------------------

RECURSIVE GCDFunc(_, _)
GCDFunc(m, n) == IF n = 0 THEN m ELSE GCDFunc(n, m % n)

Divides(d, n) == \E k \in Int : n = d * k

CommonDivisors(m, n) == {d \in 1..((IF m > n THEN m ELSE n) + 1) : Divides(d, m) /\ Divides(d, n)}

-----------------------------------------------------------------------------

TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ b0 \in 1..N
          /\ done \in BOOLEAN
          /\ (done = FALSE => x > 0 /\ y > 0)

GCDInvariant == GCDFunc(x, y) = GCDFunc(A, b0)

SafetyInvariant == /\ TypeOK
                   /\ GCDInvariant

-----------------------------------------------------------------------------

Init == /\ b0 \in 1..N
        /\ x = A
        /\ y = b0
        /\ done = FALSE

Swap == /\ done = FALSE
        /\ x < y
        /\ x' = y
        /\ y' = x
        /\ b0' = b0
        /\ done' = done

Subtract == /\ done = FALSE
            /\ x >= y
            /\ x' = x - y
            /\ y' = y
            /\ b0' = b0
            /\ done' = IF x - y = 0 THEN TRUE ELSE FALSE

Halt == /\ done = TRUE
        /\ UNCHANGED vars

Step == Swap \/ Subtract

Next == Step \/ Halt

Fairness == WF_vars(Step)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

Termination == <>(done = TRUE)

CorrectnessAtTermination == done = TRUE => (IF x = 0 THEN y ELSE x) = GCDFunc(A, b0)

BoundedValues == /\ x <= A + N
                 /\ y <= A + N

=============================================================================
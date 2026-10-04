-------------------------------- MODULE GCD --------------------------------

EXTENDS Naturals, Integers

CONSTANTS MaxVal

VARIABLES x, y, x0, y0, done

vars == <<x, y, x0, y0, done>>

-----------------------------------------------------------------------------

GCD(a, b) == 
    LET RECURSIVE GCDHelper(_, _)
        GCDHelper(m, n) == 
            IF n = 0 THEN m
            ELSE GCDHelper(n, m % n)
    IN IF a >= b THEN GCDHelper(a, b) ELSE GCDHelper(b, a)

-----------------------------------------------------------------------------

Init ==
    /\ x \in 1..MaxVal
    /\ y \in 1..MaxVal
    /\ x0 = x
    /\ y0 = y
    /\ done = FALSE

Swap ==
    /\ ~done
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = done

Subtract ==
    /\ ~done
    /\ x >= y
    /\ y > 0
    /\ x' = x - y
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = done

Terminate ==
    /\ ~done
    /\ (x = 0 \/ y = 0)
    /\ done' = TRUE
    /\ x' = x
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0

Next ==
    \/ Swap
    \/ Subtract
    \/ Terminate

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeInvariant ==
    /\ x \in Nat
    /\ y \in Nat
    /\ x0 \in 1..MaxVal
    /\ y0 \in 1..MaxVal
    /\ done \in BOOLEAN

PositiveOrZero ==
    /\ x >= 0
    /\ y >= 0

GCDPreserved ==
    (x > 0 \/ y > 0) => GCD(x, y) = GCD(x0, y0)

Correctness ==
    done => (IF x = 0 THEN y = GCD(x0, y0) ELSE x = GCD(x0, y0))

Invariant ==
    /\ TypeInvariant
    /\ PositiveOrZero
    /\ GCDPreserved
    /\ Correctness

-----------------------------------------------------------------------------

Termination == <>(done = TRUE)

=============================================================================
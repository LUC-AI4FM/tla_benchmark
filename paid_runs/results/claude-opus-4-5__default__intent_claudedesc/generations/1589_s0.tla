---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, Naturals

CONSTANTS MaxVal

ASSUME MaxVal \in Nat /\ MaxVal >= 1

VARIABLES x, y, x0, y0, done

vars == <<x, y, x0, y0, done>>

Divides(a, b) == \E k \in 1..b : a * k = b

CommonDivisor(a, b) == {d \in 1..a : Divides(d, a) /\ Divides(d, b)}

GCD(a, b) == CHOOSE d \in CommonDivisor(a, b) : \A e \in CommonDivisor(a, b) : e <= d

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
    /\ x > 0
    /\ x' = x - y
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = done

Terminate ==
    /\ ~done
    /\ x = 0
    /\ done' = TRUE
    /\ x' = x
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0

Next == Swap \/ Subtract \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ x \in 0..MaxVal
    /\ y \in 1..MaxVal
    /\ x0 \in 1..MaxVal
    /\ y0 \in 1..MaxVal
    /\ done \in BOOLEAN

CorrectResult == done => (y = GCD(x0, y0))

Termination == <>(done = TRUE)

==========================================================================
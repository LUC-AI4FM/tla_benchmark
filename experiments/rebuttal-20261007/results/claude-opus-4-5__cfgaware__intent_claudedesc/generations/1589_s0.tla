---------------------------- MODULE GCD ----------------------------
EXTENDS Integers, Naturals

CONSTANT MaxVal

VARIABLES x, y, x0, y0, done

vars == <<x, y, x0, y0, done>>

Divides(a, b) == \E k \in 1..b : a * k = b

DivisorsOf(n) == {d \in 1..n : Divides(d, n)}

CommonDivisors(a, b) == DivisorsOf(a) \cap DivisorsOf(b)

MathGCD(a, b) == CHOOSE d \in CommonDivisors(a, b) : \A e \in CommonDivisors(a, b) : e <= d

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
    /\ done' = FALSE

Subtract ==
    /\ ~done
    /\ x >= y
    /\ x > 0
    /\ x' = x - y
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = FALSE

Terminate ==
    /\ ~done
    /\ x = 0
    /\ done' = TRUE
    /\ UNCHANGED <<x, y, x0, y0>>

Next == Swap \/ Subtract \/ Terminate

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(done = TRUE)

Invariant == done => (y = MathGCD(x0, y0))

=============================================================================
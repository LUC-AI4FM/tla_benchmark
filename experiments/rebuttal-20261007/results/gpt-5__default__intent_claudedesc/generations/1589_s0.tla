----------------------------- MODULE EuclidGCD -----------------------------

EXTENDS Naturals

CONSTANT MaxVal
ASSUME MaxVal = 20

VARIABLES a, b, a0, b0

vars == << a, b, a0, b0 >>

Terminated == a = 0

Init ==
  /\ a \in 1..MaxVal
  /\ b \in 1..MaxVal
  /\ a0 = a
  /\ b0 = b

Next ==
  IF Terminated THEN
    /\ UNCHANGED vars
  ELSE
    LET aa == IF a < b THEN b ELSE a
        bb == IF a < b THEN a ELSE b
    IN  /\ a' = aa - bb
        /\ b' = bb
        /\ a0' = a0
        /\ b0' = b0

Spec == Init /\ [][Next]_vars

Divides(d, n) ==
  /\ d \in 1..MaxVal
  /\ n \in 0..MaxVal
  /\ \E k \in 0..MaxVal: n = d * k

GCD(n, m) ==
  CHOOSE g \in 1..MaxVal:
    /\ Divides(g, n)
    /\ Divides(g, m)
    /\ \A h \in 1..MaxVal:
         (Divides(h, n) /\ Divides(h, m)) => h <= g

TypeInv ==
  /\ a \in 0..MaxVal
  /\ b \in 1..MaxVal
  /\ a0 \in 1..MaxVal
  /\ b0 \in 1..MaxVal

GCDInvariant ==
  GCD(a, b) = GCD(a0, b0)

SafetyInvariant ==
  Terminated => b = GCD(a0, b0)

Safety == []SafetyInvariant

Liveness == <>Terminated

============================================================================
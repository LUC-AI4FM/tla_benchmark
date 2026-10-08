------------------------------ MODULE Euclid ------------------------------
EXTENDS Integers

CONSTANT MaxVal

VARIABLES a,b,initA,initB
vars == <<a,b,initA,initB>>

Init ==
  /\ a \in 1..MaxVal
  /\ b \in 1..MaxVal
  /\ initA = a
  /\ initB = b

MAX(x,y) == IF x > y THEN x ELSE y

Inv ==
  a = 0 =>
    /\ Mod(initA, b) = 0
    /\ Mod(initB, b) = 0
    /\ \A d \in 1..MAX(initA, initB) :
          (Mod(initA,d)=0 /\ Mod(initB,d)=0) => d <= b

Next ==
  \/ (a = 0) /\ UNCHANGED <<a,b>> /\ UNCHANGED <<initA, initB>>
  \/ (a > 0) /\ LET a1 == IF a < b THEN b ELSE a
                b1 == IF a < b THEN a ELSE b
           IN
             /\ a' = a1 - b1
             /\ b' = b1
             /\ UNCHANGED <<initA, initB>>

Spec ==
  Init /\ [][Next]_vars

Safety == []Inv
Liveness == []<>(a = 0)

=============================================================================
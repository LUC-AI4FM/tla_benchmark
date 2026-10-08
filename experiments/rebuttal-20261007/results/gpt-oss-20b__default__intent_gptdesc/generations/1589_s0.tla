MODULE Euclid

EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxVal, OrigA, OrigB

VARIABLE a, b

GCD(x,y) == IF y = 0 THEN x ELSE GCD(y, Mod(x,y))

Init == a = OrigA /\ b = OrigB

Subtract ==
    /\ a > 0
    /\ b > 0
    /\ IF a > b THEN
           a' = a - b /\ b' = b
       ELSE
           a' = a /\ b' = b - a

Next == Subtract

Spec == Init /\ [][Next]_<<a,b>>

PositivityInvariant == (a > 0 /\ b > 0) \/ (a = 0 \/ b = 0)

GCDInvariant == GCD(a,b) = GCD(OrigA, OrigB)

TerminationLiveness == <> (a = 0 \/ b = 0)
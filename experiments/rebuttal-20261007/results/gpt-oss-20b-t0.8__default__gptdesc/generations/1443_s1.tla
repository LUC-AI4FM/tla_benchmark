--------------------------- MODULE SmallSM ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

IsOne == (x = 1)

Done == (x = 2)

Wrap == (x = 2) /\ x' = 0

Step    == x' = (x + 1) Mod 3
Stutter == x' = x

Next == Step \/ Stutter

Init == x = 0

CoverageCheck ==
   LET c1 = TLCGet("IsOne") ,
       c2 = TLCGet("Done") ,
       c3 = TLCGet("Wrap")
   IN  c1 = 1 /\ c2 = 1 /\ c3 = 1

Spec == Init /\ [] [Next]_ <<x>> /\ [] CoverageCheck
====================================================================
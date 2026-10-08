MODULE SmallSM
EXTENDS Naturals, Integers

VARIABLES x

Init == x = 0

Next == x' = (x + 1) Mod 3

IsOne == x = 1
IsDone == x = 2
Wrap   == x = 2 /\ x' = 0

Spec == Init /\ [] (Next \/ x'=x)

CHECK (TLCGet("StateCoverage")["IsOne"] = 1) /\
      (TLCGet("StateCoverage")["IsDone"] = 1) /\
      (TLCGet("StateCoverage")["Wrap"] = 1)
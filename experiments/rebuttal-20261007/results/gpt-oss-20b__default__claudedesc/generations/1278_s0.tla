MODULE SimpleS
EXTENDS Integers

VARIABLE s

Init == s = 0

StutterStep == s' = s
NonStutterStep == (0 <= s') /\ (s' <= 9) /\ (s' Mod 2 = 0)

Next == StutterStep \/ NonStutterStep

Spec == Init /\ [] (Next)
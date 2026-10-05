---------------------------- MODULE spec ----------------------------
EXTENDS Integers

VARIABLE s

Next(var) ==
    \E val \in {0, 1} :
        /\ val > 0
        /\ var' = val

Init == s = 23

Spec == Init /\ [][Next(s)]_s

Inv == s /= 0

=======================================================================
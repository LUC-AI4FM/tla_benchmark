---------------------------- MODULE Specification ----------------------------

EXTENDS Integers

VARIABLES s

Next(var) ==
    \E v \in 0..1 :
        /\ var' = v
        /\ v > 0

Init == s = 23

Spec == Init /\ [][Next(s)]_s

Inv == s # 0

=============================================================================
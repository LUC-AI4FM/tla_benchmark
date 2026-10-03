---- MODULE SimpleModel ----
EXTENDS Integers

VARIABLES s

Next(var) == \E v \in 0..1 :
                /\ var' = v
                /\ var' > 0

Init == s = 23

Next == [Next(s)]_s

Inv == s /= 0

Spec == Init /\ [][Next]_s

=============================================================================
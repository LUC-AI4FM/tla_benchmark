------------------------------ MODULE SimpleVector ------------------------------
EXTENDS Naturals, Integers

CONSTANTS Dist, Const

VARIABLE c, v

INDEX == 1..5
CONTROL_VALUES == INDEX

Init ==
    /\ c \in CONTROL_VALUES
    /\ v = [i \in INDEX |-> 0]

Next ==
    /\ c' = c
    /\ IF c = Dist THEN
           v' = [v EXCEPT ![Dist] = Const]
       ELSE
           v' = v

Spec == Init /\ [][Next]_<<c, v>>

SafetyInvariant ==
    /\ \A i \in INDEX : v[i] \in Int
    /\ [] (c' = c)
    /\ [] ((c = Dist) => v'[Dist] = Const)
    /\ [] ((c # Dist) => \A i \in INDEX : v'[i] = v[i])

=============================================================================
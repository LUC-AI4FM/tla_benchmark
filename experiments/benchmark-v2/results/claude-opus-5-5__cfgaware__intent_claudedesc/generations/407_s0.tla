---- MODULE PrintStates ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ PrintT(<<"Init", "x", 1, "y", 1>>)
    /\ x = 1
    /\ y = 1

Stutter ==
    /\ PrintT(<<"Next: stutter from", x, y>>)
    /\ UNCHANGED <<x, y>>

Assign ==
    /\ \E v \in {1, 2, 3} :
          /\ PrintT(<<"Next: assign x from", x, "to", v>>)
          /\ x' = v
    /\ y' = 1

Next ==
    \/ Stutter
    \/ Assign

Inv == TRUE

Spec == Init /\ [][Next]_vars
====
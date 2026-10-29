---- MODULE PrimeOpArgTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1, 2}

Init ==
    /\ x = [i \in Dom |-> 0]
    /\ y = [i \in Dom |-> 0]

\* Operator whose EXCEPT update is based on the PRIMED argument d'.
\* After d' is set, d'[1] = 1, so y'[1] must equal 1.
PrimedOp(d) ==
    /\ d' = [d EXCEPT ![1] = 1]
    /\ y' = [d' EXCEPT ![2] = 2]

\* Operator whose EXCEPT update is based on the UNPRIMED argument d.
\* d[1] is still 0 in the current state, so y'[1] must equal 0.
UnprimedOp(d) ==
    /\ d' = [d EXCEPT ![1] = 1]
    /\ y' = [d EXCEPT ![2] = 2]

Next ==
    \/ /\ x[1] = 0
       /\ PrimedOp(x)
       /\ PrintT(<<"primed branch", x', y'>>)
       /\ Assert(y' = [i \in Dom |-> i], "Failure: primed operator argument")
    \/ /\ x[1] = 0
       /\ UnprimedOp(x)
       /\ PrintT(<<"unprimed branch", x', y'>>)
       /\ Assert(y' = [i \in Dom |-> IF i = 1 THEN 0 ELSE 2],
                 "Failure: unprimed operator argument")
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in [Dom -> 0..2]
    /\ y \in [Dom -> 0..2]

XInv == x[2] = 0

YInv == y[1] = x[1] \/ y = [i \in Dom |-> IF i = 1 THEN 0 ELSE 2] \/ y = [i \in Dom |-> 0]

====
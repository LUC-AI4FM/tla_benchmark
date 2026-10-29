---------------------------- MODULE PrimingTest ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1, 2}

\* Operator whose EXCEPT update is based on the primed value of its argument d
PrimedUpd(d, e) == e' = [d' EXCEPT ![1] = 3]

\* Operator whose EXCEPT update is based on the unprimed value of its argument d
UnprimedUpd(d, e) == e' = [d EXCEPT ![1] = 3]

Init ==
    /\ x = [i \in Dom |-> 0]
    /\ y = [i \in Dom |-> 0]

\* Branch 1: x' is fixed first, then y' is computed from x' via d'
A ==
    /\ x' = [i \in Dom |-> 2]
    /\ PrimedUpd(x, y)
    /\ PrintT(<<"A", x, x', y'>>)
    /\ Assert(y' = [x' EXCEPT ![1] = 3],
              "Failure: priming of operator argument d' in EXCEPT")
    /\ Assert(y'[2] = x'[2],
              "Failure: y'[2] should equal x'[2] in branch A")

\* Branch 2: x' is changed, but y' is computed from the old x via d
B ==
    /\ x' = [x EXCEPT ![2] = 5]
    /\ UnprimedUpd(x, y)
    /\ PrintT(<<"B", x, x', y'>>)
    /\ Assert(y' = [x EXCEPT ![1] = 3],
              "Failure: unprimed operator argument d in EXCEPT")
    /\ Assert(y'[2] = x[2],
              "Failure: y'[2] should equal x[2] in branch B")

Next ==
    \/ A
    \/ B
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Constraint ==
    /\ \A i \in Dom : x[i] <= 5
    /\ \A i \in Dom : y[i] <= 5

Inv ==
    /\ x \in [Dom -> {0, 2, 5}]
    /\ y \in [Dom -> {0, 2, 3, 5}]
    /\ x[1] \in {0, 2}
    /\ y[1] \in {0, 3}

=============================================================================
---- MODULE PrimeOperatorTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1, 2}

TypeOK ==
    /\ x \in [Dom -> Nat]
    /\ y \in [Dom -> Nat]

Init ==
    /\ x = [i \in Dom |-> i]
    /\ y = [i \in Dom |-> 0]

\* Operator whose EXCEPT update is applied to the primed argument d'
UsePrimed(d, e) == e' = [d' EXCEPT ![1] = 42]

\* Operator whose EXCEPT update is applied to the unprimed argument d
UseUnprimed(d, e) == e' = [d EXCEPT ![1] = 42]

\* Branch 1: priming happens inside the operator body (d')
PrimedBranch ==
    /\ x' = [x EXCEPT ![2] = 3]
    /\ UsePrimed(x, y)
    /\ PrintT(<<"primed", x', y'>>)
    /\ Assert(y' = [i \in Dom |-> IF i = 1 THEN 42 ELSE x'[2]],
              "Primed operator argument did not yield next-state value")
    /\ Assert(y'[2] = 3,
              "d' inside EXCEPT should refer to the next-state value of x")

\* Branch 2: operator uses the unprimed argument d
UnprimedBranch ==
    /\ x' = [x EXCEPT ![2] = 3]
    /\ UseUnprimed(x, y)
    /\ PrintT(<<"unprimed", x', y'>>)
    /\ Assert(y' = [i \in Dom |-> IF i = 1 THEN 42 ELSE x[2]],
              "Unprimed operator argument did not yield current-state value")

Stutter == UNCHANGED vars

Next ==
    \/ PrimedBranch
    \/ UnprimedBranch
    \/ Stutter

Spec == Init /\ [][Next]_vars

====
------------------------------ MODULE PrimeTest ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

D == {1, 2}

Init ==
    /\ x = [i \in D |-> 0]
    /\ y = [i \in D |-> 0]

\* Uses d' inside the EXCEPT update, so it refers to the next-state value
\* of the variable passed as the argument.
UsePrimed(d) == y' = [d' EXCEPT ![2] = 5]

\* Uses d unprimed inside the EXCEPT update, so it refers to the
\* current-state value of the variable passed as the argument.
UseUnprimed(d) == y' = [d EXCEPT ![2] = 5]

\* Branch 1: x[1] changes to 1, and y' is built from x'.
PrimedBranch ==
    /\ x[1] = 0
    /\ x' = [x EXCEPT ![1] = 1]
    /\ UsePrimed(x)
    /\ PrintT(<<"primed branch", x', y'>>)
    /\ Assert(y' = [i \in D |-> IF i = 1 THEN 1 ELSE 5],
              "Failure: UsePrimed(x) did not use the next-state value of x")

\* Branch 2: x[1] changes to 2, and y' is built from the current x.
UnprimedBranch ==
    /\ x[1] = 0
    /\ x' = [x EXCEPT ![1] = 2]
    /\ UseUnprimed(x)
    /\ PrintT(<<"unprimed branch", x', y'>>)
    /\ Assert(y' = [i \in D |-> IF i = 1 THEN 0 ELSE 5],
              "Failure: UseUnprimed(x) did not use the current-state value of x")

Stutter == UNCHANGED vars

Next ==
    \/ PrimedBranch
    \/ UnprimedBranch
    \/ Stutter

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in [D -> 0..2]
    /\ y \in [D -> 0..5]

\* In every reachable state, y agrees with x at index 1.
\* This holds after the primed branch, and initially.
\* After the unprimed branch, y[1] = 0 while x[1] = 2.
YConsistent ==
    \/ y[1] = x[1]
    \/ (x[1] = 2 /\ y[1] = 0)

=============================================================================
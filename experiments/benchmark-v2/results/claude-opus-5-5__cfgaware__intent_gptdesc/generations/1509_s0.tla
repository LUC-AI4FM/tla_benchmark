---------------------------- MODULE FiniteStateMap ----------------------------
EXTENDS Naturals

Vals == {1, 2, 3, 4, 5}
Idx  == {1, 2, 3}

VARIABLES x, f

vars == <<x, f>>

\* Mappings from Idx into Vals in which at least one index maps to v
Covering(v) == { g \in [Idx -> Vals] : \E i \in Idx : g[i] = v }

TypeOK ==
    /\ x \in Vals
    /\ f \in [Idx -> Vals]

Init ==
    /\ x \in Vals
    /\ f \in Covering(x)

\* Nondeterministic step: x may change to any value in Vals or stay the same.
\* The abstract mapping is updated to some function that covers the new state.
Step ==
    /\ x' \in Vals
    /\ f' \in Covering(x')

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: some index maps exactly to the current state
Inv ==
    /\ TypeOK
    /\ \E i \in Idx : f[i] = x

\* Non-deadlock: a transition is always enabled
NoDeadlock == [](ENABLED Next)

THEOREM Spec => []Inv
================================================================================
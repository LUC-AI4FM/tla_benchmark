------------------------------ MODULE TinySetMachine ------------------------------

EXTENDS TLC, Naturals

CONSTANTS 
    ExpectedFullSet,
    ExpectedGainThree

VARIABLES x, y

vars == << x, y >>

Init ==
    /\ y \subseteq {1, 2, 3}
    /\ x \subseteq y

Next ==
    /\ y' = y
    /\ x' \subseteq y'

\* State predicate: x is the full set {1,2,3}
FullSet ==
    x = {1, 2, 3}

\* Action predicate: element 3 is gained in the transition
GainThree ==
    /\ ~(3 \in x)
    /\   3 \in x'

\* Basic safety/type invariant
TypeInv ==
    /\ x \subseteq y
    /\ y \subseteq {1, 2, 3}

\* Use TLC to inspect named-state exploration metadata and assert expected counts.
\* These assertions are written as state predicates so they can be added as invariants in a TLC model.
CountAssertions ==
    /\ Assert(TLCGet("FullSet") = ExpectedFullSet, 
              "Unexpected count for FullSet")
    /\ Assert(TLCGet("GainThree") = ExpectedGainThree, 
              "Unexpected count for GainThree")

\* No full temporal Spec operator and no fairness.
Spec ==
    Init /\ Next

=============================================================================
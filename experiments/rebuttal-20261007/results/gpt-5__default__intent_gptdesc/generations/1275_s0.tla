----------------------------- MODULE StableBinary -----------------------------
EXTENDS Naturals

CONSTANTS UnusedConst

VARIABLES x

Binary == {0, 1}

Init ==
  \E b \in Binary:
    /\ x = b
    /\ x < 1

Next == UNCHANGED x

vars == << x >>

Spec == Init /\ [][Next]_vars

Inv == x < 1

Stable == [] UNCHANGED x

THEOREM SpecImpliesInvariant == Spec => [] Inv

THEOREM SpecImpliesStability == Spec => Stable
=============================================================================
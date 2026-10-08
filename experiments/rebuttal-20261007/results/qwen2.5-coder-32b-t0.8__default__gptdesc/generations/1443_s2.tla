------------------------------ MODULE StateMachine ------------------------------

EXTENDS Naturals, TLC

CONSTANTS

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x' = (x + 1) % 3
    \/ x' = x

StateIsOne == x = 1
WorkDone == x = 2
WrapAround == x = 2 /\ x' = 0

Spec ==
    INIT Init
    /\ [](Init /\ [][Next]_<<x>>)

Invariants ==
    /\ \/ x \in {0, 1, 2}
    /\ \/ StateIsOne => TRUE
    /\ \/ WorkDone => TRUE
    /\ \/ WrapAround => TRUE

Liveness ==
    <>[](StateIsOne)
    /\ <>[](WorkDone)
    /\ <>[](WrapAround)

TLCSpec == Spec /\ Invariants /\ Liveness

CoverPredicates ==
    TLCGet("NamedStateCoverage") = <<1, 1, 1>>

=============================================================================
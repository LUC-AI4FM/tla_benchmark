------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    \* No constants needed for this simple state machine

VARIABLES x

(* --algorithm SmallStateMachine

variables x = 0;

next == \/ /\ x = 0 \/ x = 1 \/ x = 2
          /\ x' = (x + 1) % 3

Spec == /\ Init
        /\ [][Next]_<<x>>

Init == x = 0

Next == \/ x # 2 /\ x' = (x + 1)
        \/ x = 2 /\ x' = 0

AtOne   == x = 1
Done    == x = 2
Wrap    == x = 2 /\ x' = 0

Invariants ==
    /\ \/ x = 0
       \/ x = 1
       \/ x = 2

\* TLC-specific checks
TLCSpec ==
    Spec /\ <>(AtOne) /\ <>(Done) /\ <>(Wrap)
    /\ TLCGet("NamedStateCoverage") = <<3>>

==*)
=============================================================================
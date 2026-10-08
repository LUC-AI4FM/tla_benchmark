---------------------------- MODULE SimpleStateMachine ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE state

TypeInvariant == state \in (0..9) /\ state % 2 = 0

Init == state = 0

Next == IF TypeInvariant
        THEN state' \in {s \in (0..9) : s % 2 = 0}
        ELSE FALSE

Spec == Init /\ [][Next]_state

THEOREM Spec => []TypeInvariant
=============================================================================
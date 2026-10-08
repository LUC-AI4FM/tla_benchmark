------------------------------ MODULE BoundedStateMachine ------------------------------
EXTENDS Naturals

CONSTANTS Domain, InitVal

VARIABLE state

(* Derived constants *)
SubRange1 == {1, 2, 3}
SubRange2 == {7, 8}

TypeInvariant == state ∈ Domain

Init == state = InitVal

Next ==
    \/ state' = 0
    \/ (state ∈ Domain /\ state' ∈ SubRange1)
    \/ (state = 5 /\ state' ∈ SubRange2)

Spec == Init /\ [][Next]_state

Invariant == TypeInvariant /\ (state = InitVal)

============================================================================
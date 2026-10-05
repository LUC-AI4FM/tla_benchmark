---------------------------- MODULE specification ----------------------------

VARIABLE state

\* The set of valid (safe) values: even integers in 0..9
ValidValues == {0, 2, 4, 6, 8}

\* Initial condition: state starts at 0
Init == state = 0

\* Next state relation: state can transition to any valid value (even and in 0..9)
\* This includes stuttering (state remains unchanged)
Next == state' \in ValidValues

\* Safety invariant: state must always be in the valid range and even
Safety == state \in ValidValues

\* Type invariant (equivalent to Safety in this specification)
TypeOK == state \in 0..9 /\ state % 2 = 0

\* The complete specification with stuttering allowed
Spec == Init /\ [][Next]_state

=============================================================================
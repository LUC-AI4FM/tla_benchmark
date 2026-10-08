---------------------------- MODULE EvenDigitStateMachine ----------------------------
EXTENDS Integers

VARIABLES state

\* The set of valid states: even digits from 0 to 9
ValidStates == {0, 2, 4, 6, 8}

\* Safety invariant: state must be an integer in 0..9 and must be even
TypeInvariant == state \in 0..9
EvenInvariant == state % 2 = 0
SafetyInvariant == TypeInvariant /\ EvenInvariant

\* Alternative formulation: state must be in the set of valid states
InValidStates == state \in ValidStates

\* Initial condition: state equals 0
Init == state = 0

\* Next state relation: any transition that results in a valid state
\* This allows non-deterministic choice of any valid successor state
Next == state' \in ValidStates

\* Stuttering step: state remains unchanged
Stutter == UNCHANGED state

\* Full next-state relation including stuttering
NextOrStutter == Next \/ Stutter

\* Temporal specification with stuttering closure
Spec == Init /\ [][Next]_state

\* Safety properties expressed as temporal formulas
AlwaysSafe == []SafetyInvariant
AlwaysInValidStates == []InValidStates
AlwaysInRange == [](state \in 0..9)
AlwaysEven == [](state % 2 = 0)

===================================================================================
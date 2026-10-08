------------------------------- MODULE CoffeeCan -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS InitBlack, InitWhite

VARIABLES Black, White

Init == /\ Black = InitBlack
        /\ White = InitWhite
        /\ Black + White > 0

Next ==
    \/ /\ Black >= 2
       /\ Black' = Black - 1
       /\ White' = White
    \/ /\ White >= 2
       /\ Black' = Black
       /\ White' = White - 1
    \/ /\ Black >= 1
       /\ White >= 1
       /\ Black' = Black - 1
       /\ White' = White + 1

Spec ==
    /\ Init
    /\ [][Next]_<<Black, White>>
    /\ WF_next(<<Black, White>>)

\* Safety: every transition strictly decreases the total number of beans by exactly one, until termination.
Safety == [](Black' + White' < Black + White \/ Black' + White' = 0)

\* Termination: the process inevitably reaches a state with exactly one bean remaining (no further two-bean selections possible).
Termination == <>[](Black' + White' = 1)

\* Invariant: the parity (evenness/oddness) of the number of white beans is preserved by every transition.
ParityInvariant == [](White % 2 = White' % 2)

\* Final-state characterization: prove that the color of the single remaining bean is determined solely by the initial parity of white beans — if the initial white count is even, the final bean is black; if odd, the final bean is white.
FinalStateCharacterization == <>(Black + White = 1) => (White % 2 = 0 => Black = 1 /\ White = 0 \/ White % 2 = 1 => Black = 0 /\ White = 1)

=============================================================================
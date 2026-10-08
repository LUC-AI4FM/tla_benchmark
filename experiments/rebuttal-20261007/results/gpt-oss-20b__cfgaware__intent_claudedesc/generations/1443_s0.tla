------------------------------ MODULE Counter ------------------------------
EXTENDS Integers

VARIABLE counter

Init == counter = 0

Next == counter' = (counter + 1) \bmod 3

PossibleCounter2 == (counter = 2) _POSSIBLE
PossibleCounter1 == (counter = 1) _POSSIBLE
WrapAround      == (counter' = 0 /\ counter = 2) _POSSIBLE

Spec == Init /\ [][Next]_<<counter>>

Postcondition == #(PossibleCounter2) = 1 /\ #(PossibleCounter1) = 1 /\ #(WrapAround) = 1

=============================================================================
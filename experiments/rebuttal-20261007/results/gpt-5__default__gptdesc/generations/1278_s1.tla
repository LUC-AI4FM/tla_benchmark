----------------------------- MODULE SmallTemporalSystem -----------------------------

EXTENDS Integers

CONSTANTS D \* Unused placeholder constant

VARIABLES s

F(var) == /\ var \in 0..9
          /\ var % 2 = 0

Init == s = 0

Next == F(s')

Spec == Init /\ [] [Next]_s

=====================================================================================
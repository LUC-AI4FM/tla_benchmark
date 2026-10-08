------------------------------ MODULE TinySM ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS
  ExpectedFullSet == 1
  ExpectedGainThree == 2

VARIABLES x, y

Init ==
  /\ y \subseteq {1,2,3}
  /\ x \subseteq y

Next ==
  /\ y' = y
  /\ x' \subseteq y'

Inv ==
  x \subseteq y

FullSet ==
  x = {1,2,3}

GainThree ==
  3 \in x' \ x

Spec == Init /\ [][Next]_<<x,y>> /\ Inv

ASSUME
  TLCGet("FullSet") = ExpectedFullSet
  /\ TLCGet("GainThree") = ExpectedGainThree

=============================================================================
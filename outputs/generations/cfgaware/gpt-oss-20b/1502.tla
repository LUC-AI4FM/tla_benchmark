------------------------------ MODULE SmallSM ------------------------------
CONSTANTS Op, Forty2
VARIABLE x

Init == 
  /\ x = 0

Next ==
  /\ x' \in Op(x)

SubsetOpSet(a) == a \subseteq Op(a)
SubsetOfFortyTwo(b) == b \subseteq {Forty2}

=============================================================================
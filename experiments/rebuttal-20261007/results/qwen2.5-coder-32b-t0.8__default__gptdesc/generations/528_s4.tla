------------------------------- MODULE SmallPlusCalSpec -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS vars

VARIABLES x, y, pc

Init == 
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "start"

Next ==
  \/ /\ pc = "start"
     /\ x' = x \cup {"c"}
     /\ y' = <<y[1], 4, y[3]>>
     /\ PrintT(x', y')
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<x, y>>
     /\ pc' = pc

Terminating ==
  <>[](pc = "Done")

Spec ==
  Init /\ [][Next]_<<x, y, pc>> /\ Terminating

=============================================================================
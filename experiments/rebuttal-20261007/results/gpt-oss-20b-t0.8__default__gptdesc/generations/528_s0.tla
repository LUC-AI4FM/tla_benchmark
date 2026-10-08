MODULE SmallPlusCal

EXTENDS Naturals, Sequences, TLC

VARIABLES x, y, pc

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1,2,3>>
  /\ pc = "Start"

Step ==
  /\ pc = "Start"
  /\ x' = x \cup {"c"}
  /\ y' = <<y[1], 4, y[3]>>
  /\ pc' = "Done"

Stutter ==
  /\ pc = "Done"
  /\ pc' = pc
  /\ x' = x
  /\ y' = y

Next == Step \/ Stutter

Spec == Init /\ [][Next]_{x,y,pc}

Termination == <> (pc = "Done")
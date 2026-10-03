---- MODULE SmallPlusCal ----
EXTENDS TLC, Integers, Sequences

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Start"

Step ==
  /\ pc = "Start"
  /\ x' = x \cup {"c"}
  /\ y' = [y EXCEPT ![2] = 4]
  /\ pc' = "Done"
  /\ PrintT([x |-> x', y |-> y'])

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ x \subseteq {"a", "b", "c"}
  /\ y \in Seq(Int)
  /\ Len(y) = 3
  /\ pc \in {"Start", "Done"}

Termination == <> (pc = "Done")
====
----------------------------- MODULE TinyPlusCalModel -----------------------------
EXTENDS Integers, Sequences, TLC

VARIABLES x, y, pc

vars == << x, y, pc >>

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Start"

DoStep ==
  /\ pc = "Start"
  /\ x' = x \cup {"c"}
  /\ y' = [y EXCEPT ![2] = 4]
  /\ PrintT(<<"x", x'>>)
  /\ PrintT(<<"y", y'>>)
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == DoStep \/ Terminating

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ x \subseteq {"a", "b", "c"}
  /\ y \in [1..3 -> Int]
  /\ pc \in {"Start", "Done"}

Termination == <> (pc = "Done")
================================================================================
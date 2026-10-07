---- MODULE SmallPlusCal ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Dummy

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
  /\ PrintT(<<"x:", x', " y:", y'>>)
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  DoStep \/ Terminating

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  /\ x \subseteq {"a", "b", "c"}
  /\ y \in Seq(Nat) /\ Len(y) = 3
  /\ pc \in {"Start", "Done"}

Termination ==
  <> (pc = "Done")

====
----------------------------- MODULE TinyPlusCalModel -----------------------------
EXTENDS TLC, Sequences, Naturals

CONSTANTS Dummy

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
  /\ PrintT("x' = ", x') = x'
  /\ PrintT("y' = ", y') = y'
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ x' = x
  /\ y' = y
  /\ pc' = pc

Next == DoStep \/ Terminating

Spec == Init /\ [][Next]_vars

(*
  Safety invariants
*)
TypeInv ==
  /\ x \subseteq {"a", "b", "c"}
  /\ {"a", "b"} \subseteq x
  /\ DOMAIN y = 1..3
  /\ y[1] = 1
  /\ y[3] = 3
  /\ y[2] \in {2, 4}
  /\ pc \in {"Start", "Done"}

StartStateInv ==
  pc = "Start" => /\ x = {"a", "b"} /\ y = <<1, 2, 3>>

DoneStateInv ==
  pc = "Done" => /\ x = {"a", "b", "c"} /\ y = <<1, 4, 3>>

Safety == TypeInv /\ StartStateInv /\ DoneStateInv

(*
  Liveness property: eventual termination
*)
Termination == <> (pc = "Done")
=============================================================================
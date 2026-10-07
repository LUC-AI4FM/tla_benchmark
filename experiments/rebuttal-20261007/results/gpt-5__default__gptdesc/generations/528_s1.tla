----------------------------- MODULE SmallPlusCal -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS Dummy

VARIABLES x, y, pc

vars == << x, y, pc >>

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Start"

Step ==
  /\ pc = "Start"
  /\ LET newX == x \cup {"c"}
         newY == [y EXCEPT ![2] = 4]
     IN /\ x' = newX
        /\ y' = newY
        /\ pc' = "Done"
        /\ PrintT(<<"x", newX, "y", newY>>) = <<"x", newX, "y", newY>>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars

(*
  Safety invariants
*)
TypeOK ==
  /\ x \subseteq {"a", "b", "c"}
  /\ y \in Seq(Nat)
  /\ Len(y) = 3
  /\ pc \in {"Start", "Done"}

UpdatedValues ==
  /\ (pc = "Start") => /\ x = {"a", "b"} /\ y = <<1, 2, 3>>
  /\ (pc = "Done")  => /\ {"a", "b"} \subseteq x /\ "c" \in x /\ Len(y) = 3 /\ y[2] = 4

(*
  Liveness property: eventual termination
*)
Termination ==
  <> (pc = "Done")

=============================================================================
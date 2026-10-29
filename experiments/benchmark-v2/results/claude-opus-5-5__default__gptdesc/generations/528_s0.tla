---- MODULE PrintValues ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = (x \union {"c"})
         /\ y' = [y EXCEPT ![2] = 4]
         /\ PrintT(<<x', y'>>)
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeOK == /\ x \subseteq {"a", "b", "c"}
          /\ y \in Seq(Nat)
          /\ pc \in {"Lbl_1", "Done"}

====
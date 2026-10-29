---- MODULE SmallPlusCal ----
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y, pc

vars == << x, y, pc >>

Init == /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = (x \cup {"c"})
         /\ y' = [y EXCEPT ![2] = 4]
         /\ PrintT(<<x', y'>>)
         /\ pc' = "Done"

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ x \subseteq {"a", "b", "c"}
          /\ y \in Seq(Nat)
          /\ pc \in {"Lbl_1", "Done"}

====
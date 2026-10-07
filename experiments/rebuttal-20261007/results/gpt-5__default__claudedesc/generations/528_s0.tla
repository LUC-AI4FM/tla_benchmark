---- MODULE PlusCalTutorial ----
EXTENDS TLC

VARIABLES x, y, pc

vars == << x, y, pc >>

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ LET xNew == x \cup {"c"}
         yNew == [y EXCEPT ![2] = 4]
     IN /\ x' = xNew
        /\ y' = yNew
        /\ PrintT("x after union: ", xNew) = xNew
        /\ PrintT("y after update: ", yNew) = yNew
        /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED <<x, y, pc>>

Next ==
  Lbl_1 \/ Terminating

Spec ==
  Init /\ [][Next]_vars

Termination ==
  <> (pc = "Done")
====
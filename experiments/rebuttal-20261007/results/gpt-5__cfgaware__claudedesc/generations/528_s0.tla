---- MODULE SimplePlusCalExample ----
EXTENDS TLC, Sequences

VARIABLES x, y, pc

vars == << x, y, pc >>

(*
--algorithm Simple
variables x = {"a", "b"};
variables y = <<1, 2, 3>>;

begin
  Lbl_1:
    x := PrintT(x \cup {"c"}, "x becomes: ");
    y[2] := PrintT(4, "y[2] becomes: ");
end algorithm;
*)

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ x' = PrintT(x \cup {"c"}, "x becomes: ")
  /\ y' = [y EXCEPT ![2] = PrintT(4, "y[2] becomes: ")]
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  Lbl_1 \/ Terminating

Spec ==
  Init /\ [][Next]_vars

Termination ==
  <>(pc = "Done")

====
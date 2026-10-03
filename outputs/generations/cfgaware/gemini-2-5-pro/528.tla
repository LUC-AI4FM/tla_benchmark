---- MODULE PlusCalTranslation ----
EXTENDS TLC, Sequences, FiniteSets

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "Lbl_1"

(*
--algorithm a
variables
    x = {"a", "b"};
    y = <<1, 2, 3>>;
begin
    Lbl_1:
        x := x \cup {"c"};
        y[2] := 4;
        print <<x, y>>;
end algorithm
*)
Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ x' = x \cup {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ PrintT(<<x', y'>>)
    /\ pc' = "Done"

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lbl_1
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>[](pc = "Done")

=============================================================================
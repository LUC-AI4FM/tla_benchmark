---------------------------- MODULE PlusCalTutorial ----------------------------
EXTENDS Naturals, Sequences, TLC

(* --algorithm PlusCalTutorial
variables x = {"a", "b"}, y = <<1, 2, 3>>;
begin
    x := x \union {"c"};
    print x;
    y[2] := 4;
    print y;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = (x \union {"c"})
         /\ PrintT(x')
         /\ y' = [y EXCEPT ![2] = 4]
         /\ PrintT(y')
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
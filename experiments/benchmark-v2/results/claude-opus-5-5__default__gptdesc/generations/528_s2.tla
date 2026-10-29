---------------------------- MODULE SimplePrint ----------------------------
EXTENDS Naturals, Sequences, TLC

(* --algorithm SimplePrint
variables x = {"a", "b"}, y = <<1, 2, 3>>;
begin
  A:
    x := x \cup {"c"};
    y[2] := 4;
    print <<x, y>>;
end algorithm; *)

VARIABLES x, y, pc

vars == << x, y, pc >>

Init == /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "A"

A == /\ pc = "A"
     /\ x' = x \cup {"c"}
     /\ y' = [y EXCEPT ![2] = 4]
     /\ PrintT(<<x', y'>>)
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ x \subseteq {"a", "b", "c"}
          /\ y \in Seq(Nat)
          /\ Len(y) = 3
          /\ pc \in {"A", "Done"}

DoneCorrect == (pc = "Done") => (x = {"a", "b", "c"} /\ y = <<1, 4, 3>>)

=============================================================================
---- MODULE SmallPlusCal ----
EXTENDS Naturals, Sequences, TLC

(* --algorithm SmallPlusCal
variables x = {"a", "b"}, y = <<1, 2, 3>>;
begin
  A:
    x := x \cup {"c"};
    y[2] := 4;
    print <<x, y>>;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

TypeOK ==
    /\ x \subseteq {"a", "b", "c"}
    /\ y \in Seq(Nat)
    /\ Len(y) = 3
    /\ pc \in {"A", "Done"}

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "A"

A ==
    /\ pc = "A"
    /\ x' = x \cup {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ PrintT(x')
    /\ PrintT(y')
    /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == A \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")
\* END TRANSLATION

(* Safety invariants *)
DoneState ==
    pc = "Done" => (x = {"a", "b", "c"} /\ y = <<1, 4, 3>>)

InitialState ==
    pc = "A" => (x = {"a", "b"} /\ y = <<1, 2, 3>>)

====
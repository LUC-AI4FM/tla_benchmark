---- MODULE PlusCalIntro ----
EXTENDS TLC, Sequences

(*
--algorithm Demo
variables s = {"a", "b"};
variables seq = <<1, 2, 3>>;

begin
  Add:
    s := s \cup {"c"};
    print "After adding to set: " \o ToString(s);
  Replace:
    seq[2] := 42;
    print "After replacing in seq: " \o ToString(seq);
  Done:
    skip;
end algorithm;
*)

VARIABLES pc, s, seq

vars == << pc, s, seq >>

Init ==
  /\ pc = "Add"
  /\ s = {"a", "b"}
  /\ seq = <<1, 2, 3>>

Add ==
  /\ pc = "Add"
  /\ s' = s \cup {"c"}
  /\ seq' = seq
  /\ pc' = "Replace"
  /\ PrintT("After adding to set: " \o ToString(s'))

Replace ==
  /\ pc = "Replace"
  /\ seq' = [seq EXCEPT ![2] = 42]
  /\ s' = s
  /\ pc' = "Done"
  /\ PrintT("After replacing in seq: " \o ToString(seq'))

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Add \/ Replace \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====
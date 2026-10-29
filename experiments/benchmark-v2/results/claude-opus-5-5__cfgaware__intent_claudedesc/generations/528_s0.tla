---- MODULE PlusCalIntro ----
EXTENDS Naturals, Sequences, TLC

(* --algorithm Intro
variables s = {"a", "b"}, q = <<1, 2, 3>>;
begin
  A: s := s \union {"c"};
     print s;
  B: q[2] := 5;
     print q;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES s, q, pc

vars == << s, q, pc >>

Init == /\ s = {"a", "b"}
        /\ q = <<1, 2, 3>>
        /\ pc = "A"

A == /\ pc = "A"
     /\ s' = (s \union {"c"})
     /\ PrintT(s')
     /\ pc' = "B"
     /\ q' = q

B == /\ pc = "B"
     /\ q' = [q EXCEPT ![2] = 5]
     /\ PrintT(q')
     /\ pc' = "Done"
     /\ s' = s

Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

====
---- MODULE PlusCalIntro ----
EXTENDS Naturals, Sequences, TLC

(* --algorithm PlusCalIntro
variables
    s = {"a", "b"},
    seq = <<1, 2, 3>>;
begin
  AddElem:
    s := s \union {"c"};
    print s;
  UpdateSeq:
    seq[2] := 5;
    print seq;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES s, seq, pc

vars == << s, seq, pc >>

Init == /\ s = {"a", "b"}
        /\ seq = <<1, 2, 3>>
        /\ pc = "AddElem"

AddElem == /\ pc = "AddElem"
           /\ s' = (s \union {"c"})
           /\ PrintT(s')
           /\ pc' = "UpdateSeq"
           /\ seq' = seq

UpdateSeq == /\ pc = "UpdateSeq"
             /\ seq' = [seq EXCEPT ![2] = 5]
             /\ PrintT(seq')
             /\ pc' = "Done"
             /\ s' = s

Terminating == pc = "Done" /\ UNCHANGED vars

Next == AddElem \/ UpdateSeq \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ s \subseteq {"a", "b", "c"}
          /\ seq \in Seq(Nat)
          /\ Len(seq) = 3
          /\ pc \in {"AddElem", "UpdateSeq", "Done"}

SetInvariant == pc = "Done" => s = {"a", "b", "c"}

SeqInvariant == pc = "Done" => seq = <<1, 5, 3>>

====
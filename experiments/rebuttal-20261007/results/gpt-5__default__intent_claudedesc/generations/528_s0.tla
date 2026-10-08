----------------------------- MODULE PlusCalSetSeqDemo -----------------------------
EXTENDS TLC, Sequences, Integers

CONSTANTS NewStr, NewInt
ASSUME /\ NewStr = "gamma"
       /\ NewInt = 42

(*
--fair algorithm Demo
variables S = {"alpha", "beta"};
variables Q = <<1, 2, 3>>;
variables done = FALSE;

begin
  AddToSet:
    S := S \cup {NewStr};
    print S;

  UpdateSeq:
    Q[2] := NewInt;
    print Q;
    done := TRUE;
end algorithm
*)

VARIABLES pc, S, Q, done

vars == << pc, S, Q, done >>

Init ==
  /\ S = {"alpha", "beta"}
  /\ Q = <<1, 2, 3>>
  /\ done = FALSE
  /\ pc = "AddToSet"

AddToSet ==
  /\ pc = "AddToSet"
  /\ S' = S \cup {NewStr}
  /\ Q' = Q
  /\ done' = done
  /\ TLC!Print("Updated S: " \o ToString(S'))
  /\ pc' = "UpdateSeq"

UpdateSeq ==
  /\ pc = "UpdateSeq"
  /\ Q' = [Q EXCEPT ![2] = NewInt]
  /\ S' = S
  /\ done' = TRUE
  /\ TLC!Print("Updated Q: " \o ToString(Q'))
  /\ pc' = "Done"

Next == AddToSet \/ UpdateSeq

Spec == Init /\ [][Next]_vars /\ WF_vars(AddToSet) /\ WF_vars(UpdateSeq)

TypeOK ==
  /\ S \subseteq {"alpha", "beta", NewStr}
  /\ Q \in Seq(Int)
  /\ Len(Q) = 3
  /\ done \in BOOLEAN
  /\ pc \in {"AddToSet", "UpdateSeq", "Done"}

Termination == <> (pc = "Done" /\ done = TRUE)
=============================================================================
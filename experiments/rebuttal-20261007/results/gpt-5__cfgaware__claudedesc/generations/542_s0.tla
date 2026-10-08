------------------------------ MODULE TwoProcIncrement ------------------------------

EXTENDS Integers

(*
--algorithm Inc
variables x = 0;

process (ProcA = "ProcA")
begin
a: x := x + 1;
Done: skip;
end process;

process (ProcB = "ProcB")
begin
b: x := x + 1;
Done: skip;
end process;

end algorithm
*)

CONSTANTS
  ProcAName, ProcBName

ASSUME ProcAName = "ProcA" /\ ProcBName = "ProcB"

CONSTANTS
  ALabel, BLabel, DoneLabel

ASSUME ALabel = "a" /\ BLabel = "b" /\ DoneLabel = "Done"

VARIABLES x, pc

ProcSet == {ProcAName, ProcBName}

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = [ p \in ProcSet |-> IF p = ProcAName THEN ALabel ELSE BLabel ]

A ==
  /\ pc[ProcAName] = ALabel
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![ProcAName] = DoneLabel]

B ==
  /\ pc[ProcBName] = BLabel
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![ProcBName] = DoneLabel]

Terminating ==
  /\ pc[ProcAName] = DoneLabel
  /\ pc[ProcBName] = DoneLabel
  /\ UNCHANGED vars

Next == A \/ B \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <> (pc[ProcAName] = DoneLabel /\ pc[ProcBName] = DoneLabel)

=============================================================================
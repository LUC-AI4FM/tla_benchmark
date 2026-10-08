----------------------------- MODULE RingTwoStep -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES A, B, pc, fw

Processes == 0..(N - 1)

Left(i)  == IF i = 0 THEN N - 1 ELSE i - 1
Right(i) == IF i = N - 1 THEN 0 ELSE i + 1

vars == << A, B, pc, fw >>

Init ==
  /\ A = [ i \in Processes |-> 0 ]
  /\ B = [ i \in Processes |-> 0 ]
  /\ pc = [ i \in Processes |-> "W" ] \* "W" = not yet written; "R" = written 1, ready to read; "Done" = finished read
  /\ fw = N \* ghost: index of the (unique) first writer, or N if none has written yet

Write(i) ==
  /\ i \in Processes
  /\ pc[i] = "W"
  /\ A'  = [ A EXCEPT ![i] = 1 ]
  /\ B'  = B
  /\ pc' = [ pc EXCEPT ![i] = "R" ]
  /\ fw' = IF fw = N THEN i ELSE fw

Read(i) ==
  /\ i \in Processes
  /\ pc[i] = "R"
  /\ A'  = A
  /\ B'  = [ B EXCEPT ![i] = A[Left(i)] ]
  /\ pc' = [ pc EXCEPT ![i] = "Done" ]
  /\ fw' = fw

Next ==
  \E i \in Processes : Write(i) \/ Read(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Processes : WF_vars(Write(i))
  /\ \A i \in Processes : WF_vars(Read(i))

TypeOK ==
  /\ N \in Nat /\ N > 0
  /\ A \in [Processes -> {0, 1}]
  /\ B \in [Processes -> {0, 1}]
  /\ pc \in [Processes -> {"W", "R", "Done"}]
  /\ fw \in (Processes \cup {N})

PhaseAConsistency ==
  /\ \A i \in Processes : pc[i] = "W" => A[i] = 0
  /\ \A i \in Processes : pc[i] \in {"R", "Done"} => A[i] = 1

FirstWriterProps ==
  /\ (fw = N) <=> (\A i \in Processes : pc[i] = "W")
  /\ (fw = N) \/ (fw \in Processes /\ pc[fw] \in {"R", "Done"})
  /\ (fw = N)
     \/ (\A r \in Processes :
           r = Right(fw) => (pc[r] = "Done" => B[r] = 1))

Inv ==
  /\ TypeOK
  /\ PhaseAConsistency
  /\ FirstWriterProps

Terminated ==
  \A i \in Processes : pc[i] = "Done"

PCorrect ==
  Terminated => (\E i \in Processes : B[i] = 1)

=============================================================================
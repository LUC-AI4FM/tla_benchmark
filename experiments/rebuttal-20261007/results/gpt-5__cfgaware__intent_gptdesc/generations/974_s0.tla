---- MODULE RegularRing ----
EXTENDS Naturals

CONSTANT N

(*
  Processes are 1..N in a ring. Each process i:
  - Begins a write of 1 to its own register (making its register {0,1})
  - Completes the write (making its register {1})
  - Reads its left neighbor's register and stores the observed value in Local[i]
*)

Proc == 1..N
Values == {0, 1}
NonEmptyVals == { {0}, {1}, {0,1} }

Left(i) == IF i = 1 THEN N ELSE i - 1

VARIABLES pc, Reg, Local

vars == << pc, Reg, Local >>

PCStates == {"W0", "W1", "W2", "Done"}

Init ==
  /\ pc    = [i \in Proc |-> "W0"]
  /\ Reg   = [i \in Proc |-> {0}]
  /\ Local = [i \in Proc |-> 0]

Begin(i) ==
  /\ i \in Proc
  /\ pc[i] = "W0"
  /\ pc'   = [pc EXCEPT ![i] = "W1"]
  /\ Reg'  = [Reg EXCEPT ![i] = {0,1}]
  /\ UNCHANGED Local

Finish(i) ==
  /\ i \in Proc
  /\ pc[i] = "W1"
  /\ pc'   = [pc EXCEPT ![i] = "W2"]
  /\ Reg'  = [Reg EXCEPT ![i] = {1}]
  /\ UNCHANGED Local

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "W2"
  /\ \E v \in Reg[Left(i)]:
       /\ pc'    = [pc EXCEPT ![i] = "Done"]
       /\ Local' = [Local EXCEPT ![i] = v]
       /\ Reg'   = Reg

Next == \E i \in Proc: Begin(i) \/ Finish(i) \/ Read(i)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ Reg \in [Proc -> NonEmptyVals]
  /\ Local \in [Proc -> Values]
  /\ pc \in [Proc -> PCStates]

Inv == TypeOK

AllTerminated == \A i \in Proc: pc[i] = "Done"
SomeRead1    == \E i \in Proc: Local[i] = 1

PCorrect == [] (AllTerminated => SomeRead1)

TerminationPossible == <> AllTerminated
====================
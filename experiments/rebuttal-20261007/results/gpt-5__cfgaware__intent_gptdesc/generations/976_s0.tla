----------------------------- MODULE RingProcesses -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES reg, res, pc

Proc == 1..N

Left(i) == IF i = 1 THEN N ELSE i - 1

Init ==
  /\ reg = [ i \in Proc |-> 0 ]
  /\ res = [ i \in Proc |-> 0 ]
  /\ pc  = [ i \in Proc |-> "Start" ]

Write(i) ==
  /\ i \in Proc
  /\ pc[i] = "Start"
  /\ pc' = [pc EXCEPT ![i] = "Mid" ]
  /\ reg' = [reg EXCEPT ![i] = 1 ]
  /\ UNCHANGED res

ReadLeft(i) ==
  /\ i \in Proc
  /\ pc[i] = "Mid"
  /\ pc' = [pc EXCEPT ![i] = "Done" ]
  /\ res' = [res EXCEPT ![i] = reg[Left(i)] ]
  /\ UNCHANGED reg

Next ==
  \E i \in Proc: Write(i) \/ ReadLeft(i)

vars == << reg, res, pc >>

AllDone == \A i \in Proc: pc[i] = "Done"

TypeOK ==
  /\ reg \in [Proc -> {0,1}]
  /\ res \in [Proc -> {0,1}]
  /\ pc  \in [Proc -> {"Start","Mid","Done"}]

PCorrect ==
  AllDone => (\E i \in Proc: res[i] = 1)

Inv ==
  TypeOK /\ PCorrect

Spec ==
  /\ Init
  /\ [Next]_vars
  /\ \A i \in Proc: WF_vars(Write(i)) /\ WF_vars(ReadLeft(i))

===============================================================================
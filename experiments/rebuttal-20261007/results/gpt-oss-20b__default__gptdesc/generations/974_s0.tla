MODULE RegularRegisterAlgorithm
EXTENDS Naturals, Sequences

CONSTANT N \in Nat

VARIABLES x, y, pc

Init ==
  /\ x = [i \in 1..N |-> {0}]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "init"]

NextIndex(i) == IF i < N THEN i+1 ELSE 1

InitStep(i) ==
  /\ pc[i] = "init"
  /\ pc' = [pc EXCEPT ![i] = "write1"]
  /\ UNCHANGED <<x, y>>

WriteStep1(i) ==
  /\ pc[i] = "write1"
  /\ x' = [x EXCEPT ![i] = {0,1}]
  /\ pc' = [pc EXCEPT ![i] = "write2"]
  /\ UNCHANGED y

WriteStep2(i) ==
  /\ pc[i] = "write2"
  /\ x' = [x EXCEPT ![i] = {1}]
  /\ pc' = [pc EXCEPT ![i] = "read"]
  /\ UNCHANGED y

ReadNeighbor(i) ==
  /\ pc[i] = "read"
  /\ LET val == CHOOSE v \in x[NextIndex(i)] : TRUE
     IN y' = [y EXCEPT ![i] = val]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED x

DoneState(i) ==
  /\ pc[i] = "done"
  /\ UNCHANGED <<x, y, pc>>

ProcessStep(i) == InitStep(i) \/ WriteStep1(i) \/ WriteStep2(i) \/ ReadNeighbor(i) \/ DoneState(i)

Next == \E i \in 1..N : ProcessStep(i)

TerminationCondition == \A i \in 1..N : pc[i] = "done"

PCorrect == TerminationCondition => (\E i \in 1..N : y[i] = 1)

Inv == TerminationCondition => (\E i \in 1..N : y[i] = 1)

Spec == Init /\ [][Next]_<<x, y, pc>> /\ WF_<<x, y, pc>>(ProcessStep)
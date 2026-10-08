------------------------------ MODULE RegularReg ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES r, y, pc

Init == 
  /\ r = [i \in 1..N |-> {0}]
  /\ y = [i \in 1..N |-> {}]
  /\ pc = [i \in 1..N |-> "Start"]

WriteStep1(i) == 
  /\ i \in 1..N
  /\ pc[i] = "Start"
  /\ r[i] = {0}
  /\ r' = [r EXCEPT ![i] = {0,1}]
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "Writing2"]

WriteStep2(i) == 
  /\ i \in 1..N
  /\ pc[i] = "Writing2"
  /\ r[i] = {0,1}
  /\ r' = [r EXCEPT ![i] = {1}]
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "ReadNeighbor"]

ReadStep(i) == 
  /\ i \in 1..N
  /\ pc[i] = "ReadNeighbor"
  /\ LET j == IF i < N THEN i + 1 ELSE 1 IN
     /\ r' = r
     /\ y' = [y EXCEPT ![i] = CHOOSE v \in r[j] : TRUE]
     /\ pc' = [pc EXCEPT ![i] = "Done"]

Next == 
  ∨ i \in 1..N :
      (WriteStep1(i) \/ WriteStep2(i) \/ ReadStep(i))

TerminationCondition == ∀i \in 1..N : pc[i] = "Done"

Inv == 
  /\ ∀i \in 1..N : r[i] ⊆ {0,1} /\ r[i] ≠ {}
  /\ ∀i \in 1..N : pc[i] = "Done" => (∃j \in 1..N : y[j] = 1)

PCorrect == 
  Implies(TerminationCondition, ∃i \in 1..N : y[i] = 1)

Spec == Init /\ [][Next]_<<r,y,pc>> /\ Inv

THEOREM Correctness: Spec => []PCorrect
===============================================================================
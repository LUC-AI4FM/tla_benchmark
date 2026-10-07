```tla
MODULE ConcurrentAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES x, y, pc

Init ==
  /\ x = [i \in 0..N-1 |-> 0]
  /\ y = [i \in 0..N-1 |-> 0]
  /\ pc = [i \in 0..N-1 |-> "a"]

TypeOK == 
  /\ x \in [0..N-1 -> {0, 1}]
  /\ y \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"a", "b", "Done"}]

PastA(i) == 
  (pc[i] = "b") \/ (pc[i] = "Done")

Inv == 
  /\ TypeOK
  /\ \A i \in 0..N-1 : PastA(i) => x[i] = 1
  /\ \E i \in 0..N-1 : (pc[i] /= "Done") \/ (y[i] = 1)

Next ==
  \E i \in 0..N-1 :
    IF pc[i] = "a" THEN
      /\ x' = [x EXCEPT ![i] = 1]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "b"]
      /\ UNCHANGED <<x, y, pc>>
    ELSE IF pc[i] = "b" THEN
      /\ x' = x
      /\ y' = [y EXCEPT ![i] = x[(i-1) % N]]
      /\ pc' = [pc EXCEPT ![i] = "Done"]
      /\ UNCHANGED <<x, y, pc>>
    ELSE
      /\ UNCHANGED <<x, y, pc>>

Spec == Init /\ [][Next]_<<x, y, pc>>
           /\ \A i \in 0..N-1 : WF(Next, pc[i])

PCorrect == \E i \in 0..N-1 : y[i] = 1

THEOREM Spec => []PCorrect
PROOF BY induction
  <1>1. Base case: Init => PCorrect
    OBVIOUS
  <2>2. Inductive step: Inv /\ [Next]_<<x, y, pc>> => Inv'
    SUFFICE TO PROVE Inv' 
      <3> BY DEF Inv
        <4> CASE PastA(i)
          <5>1. pc[i] = "b"
            USE DEF PastA
          <6>2. pc[i] = "Done"
            USE DEF PastA
THEOREM Correctness == Spec => []Inv
PROOF BY induction
  <1>1. Base case: Init => Inv
    OBVIOUS
  <2>2. Inductive step: Inv /\ [Next]_<<x, y, pc>> => Inv'
    SUFFICE TO PROVE Inv' 
      <3> BY DEF Inv
        <4> CASE PastA(i)
          <5>1. pc[i] = "b"
            USE DEF PastA
          <6>2. pc[i] = "Done"
            USE DEF PastA

THEOREM Correctness2 == Spec => []Inv
PROOF BY induction
  <1>1. Base case: Init => Inv
    OBVIOUS
  <2>2. Inductive step: Inv /\ [Next]_<<x, y, pc>> => Inv'
    SUFFICE TO PROVE Inv' 
      <3> BY DEF Inv
        <4> CASE PastA(i)
          <5>1. pc[i] = "b"
            USE DEF PastA
          <6>2. pc[i] = "Done"
            USE DEF PastA
```
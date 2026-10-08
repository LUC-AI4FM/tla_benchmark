---------------------------- MODULE BakeryAlgorithm ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT NumProcs
VARIABLES choosing, number, inCS

Spec == 
  /\ choosing \in [1..NumProcs -> {TRUE, FALSE}]
  /\ number \in [1..NumProcs -> 0..MaxTicket]
  /\ inCS \in [1..NumProcs -> {TRUE, FALSE}]
  /\ Init
  /\ [][Next]_choosing /\
      [][Next]_number /\
      [][Next]_inCS

Init == 
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ number = [i \in 1..NumProcs |-> 0]
  /\ inCS = [i \in 1..NumProcs |-> FALSE]

Next == 
  \/ \E i \in 1..NumProcs :
      /\ ~choosing[i]
      /\ choosing' = [choosing EXCEPT ![i] = TRUE]
      /\ number' = number
      /\ inCS' = inCS
  \/ \E i \in 1..NumProcs :
      /\ choosing[i]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ number' = [number EXCEPT ![i] = 1 + Max([number[j] | j \in 1..NumProcs])]
      /\ inCS' = inCS
  \/ \E i \in 1..NumProcs :
      /\ choosing[i] = FALSE
      /\ inCS[i] = FALSE
      /\ \A j \in 1..NumProcs : 
          ~(choosing[j]) /\ (number[i] < number[j]) \/ (number[i] = number[j] /\ i < j)
      /\ inCS' = [inCS EXCEPT ![i] = TRUE]
      /\ choosing' = choosing
      /\ number' = number
  \/ \E i \in 1..NumProcs :
      /\ inCS[i]
      /\ inCS' = [inCS EXCEPT ![i] = FALSE]
      /\ choosing' = choosing
      /\ number' = number

Invariant == 
  \A i, j \in 1..NumProcs : 
    ~((inCS[i]) /\ (inCS[j]) /\ (i # j))

THEOREM Spec => []Invariant
=============================================================================
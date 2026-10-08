--------------------------- MODULE BakeryAlgorithm ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT NumProcs, MaxNum

VARIABLES choosing, num, inCS, readNums

Spec == 
  /\ choosing \in [1..NumProcs -> {TRUE, FALSE}]
  /\ num \in [1..NumProcs -> 0..MaxNum]
  /\ inCS \in [1..NumProcs -> {TRUE, FALSE}]
  /\ readNums \in [1..NumProcs -> SUBSET (1..NumProcs)]
  /\ Init
  /\ [][Next]_choosing
  /\ WF_vars(Next)_(choosing, num, inCS, readNums)

Init == 
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ num = [i \in 1..NumProcs |-> 0]
  /\ inCS = [i \in 1..NumProcs |-> FALSE]
  /\ readNums = [i \in 1..NumProcs |-> {}]

Next == 
  \/ \E i \in 1..NumProcs : 
    /\ choosing[i] = FALSE
    /\ num[i] = 0
    /\ inCS[i] = FALSE
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<num, inCS, readNums>>
  \/ \E i \in 1..NumProcs : 
    /\ choosing[i] = TRUE
    /\ num[i] = 0
    /\ inCS[i] = FALSE
    /\ readNums' = [readNums EXCEPT ![i] = {j \in 1..NumProcs : num[j] # 0}]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ num' = [num EXCEPT ![i] = 1 + Max({num[j] : j \in readNums'[i]} \cup {0})]
    /\ UNCHANGED inCS
  \/ \E i \in 1..NumProcs : 
    /\ choosing[i] = FALSE
    /\ num[i] # 0
    /\ inCS[i] = FALSE
    /\ \A j \in 1..NumProcs : 
      (num[j] # 0 /\ (num[j] < num[i] \/ (num[j] = num[i] /\ j < i))) => choosing[j] = FALSE
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<choosing, num, readNums>>
  \/ \E i \in 1..NumProcs : 
    /\ inCS[i] = TRUE
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ num' = [num EXCEPT ![i] = 0]
    /\ UNCHANGED <<readNums>>

Invariant == 
  /\ \A i, j \in 1..NumProcs : i # j => num[i] # num[j] \/ (num[i] = num[j] /\ i < j)
  /\ \A i \in 1..NumProcs : inCS[i] => \A j \in 1..NumProcs : i # j => ~inCS[j]
  /\ \A i \in 1..NumProcs : choosing[i] => num[i] = 0
  /\ \A i \in 1..NumProcs : inCS[i] => num[i] # 0

THEOREM Spec => []Invariant
=============================================================================
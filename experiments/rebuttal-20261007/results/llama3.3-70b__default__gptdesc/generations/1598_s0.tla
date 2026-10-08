```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, S, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ S = [i \in 1..N |-> {}]
  /\ pc = [i \in 1..N |-> "Start"]

Next ==
  \/ \E i \in 1..N :
    /\ pc[i] = "Start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ y' = 0
    /\ S' = [S EXCEPT ![i] = {}]
    /\ pc' = [pc EXCEPT ![i] = "Try1"]
    /\ UNCHANGED <<y, S, pc>>
  \/ \E i \in 1..N :
    /\ pc[i] = "Try1"
    /\ x = i
    /\ y' = i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ S' = [S EXCEPT ![i] = {}]
    /\ pc' = [pc EXCEPT ![i] = "Try2"]
    /\ UNCHANGED <<x, S, pc>>
  \/ \E i \in 1..N :
    /\ pc[i] = "Try2"
    /\ y = i
    /\ x' = 0
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ S' = [S EXCEPT ![i] = {}]
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<y, S, pc>>
  \/ \E i \in 1..N :
    /\ pc[i] = "CS"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ x' = 0
    /\ y' = 0
    /\ S' = [S EXCEPT ![i] = {}]
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<y, S, pc>>
  \/ \E i \in 1..N :
    /\ pc[i] = "Try2"
    /\ y /= i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ x' = 0
    /\ y' = 0
    /\ S' = [S EXCEPT ![i] = {}]
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<y, S, pc>>

MutualExclusion ==
  \A i, j \in 1..N : i /= j => ~(pc[i] = "CS" /\ pc[j] = "CS")

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, S, pc>>
  /\ WF_<<x, y, b, S, pc>>(Next)

THEOREM Spec => []MutualExclusion
THEOREM Spec => <><pc[1] = "CS">
```
```
MODULE FastMutualExclusion
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES x, y, b, S, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ S = [i \in 1..N |-> {}]
  /\ pc = [i \in 1..N |-> "start"]

Next ==
  \E i \in 1..N :
    IF pc[i] = "start" THEN
      /\ x = i
      /\ UNCHANGED y
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ S' = [S EXCEPT ![i] = {}]
      /\ pc' = [pc EXCEPT ![i] = "loop1"]
    ELSE IF pc[i] = "loop1" THEN
      /\ x = i
      /\ y = i
      /\ UNCHANGED b
      /\ S' = [S EXCEPT ![i] = {}]
      /\ pc' = [pc EXCEPT ![i] = "loop2"]
    ELSE IF pc[i] = "loop2" THEN
      /\ x = 0
      /\ y = 0
      /\ UNCHANGED b
      /\ S' = [S EXCEPT ![i] = {}]
      /\ pc' = [pc EXCEPT ![i] = "critical"]
    ELSE IF pc[i] = "critical" THEN
      /\ UNCHANGED x
      /\ UNCHANGED y
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ S' = [S EXCEPT ![i] = {}]
      /\ pc' = [pc EXCEPT ![i] = "start"]
    ELSE
      UNCHANGED x
      /\ UNCHANGED y
      /\ UNCHANGED b
      /\ UNCHANGED S
      /\ UNCHANGED pc

Spec ==
  Init /\ [][Next]_<<x, y, b, S, pc>>
  /\ WF_vars(Next, <<x, y, b, S, pc>>)

MutualExclusion ==
  \A i, j \in 1..N :
    pc[i] = "critical" => pc[j] # "critical"

THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]\E i \in 1..N : pc[i] = "critical"
```
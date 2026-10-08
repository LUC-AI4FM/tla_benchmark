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
  \E i \in 1..N :
    IF pc[i] = "Start" THEN
      /\ x' = i
      /\ y' = i
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ S' = [S EXCEPT ![i] = {}]
      /\ pc' = [pc EXCEPT ![i] = "Try"]
    ELSE IF pc[i] = "Try" THEN
      IF x = y THEN
        /\ y' = 0
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ S' = [S EXCEPT ![i] = {}]
        /\ pc' = [pc EXCEPT ![i] = "Start"]
      ELSE
        /\ S' = [S EXCEPT ![i] = {x}]
        /\ pc' = [pc EXCEPT ![i] = "Wait"]
    ELSE IF pc[i] = "Wait" THEN
      IF x = i THEN
        /\ y' = 0
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ S' = [S EXCEPT ![i] = {}]
        /\ pc' = [pc EXCEPT ![i] = "Start"]
      ELSE
        /\ pc' = [pc EXCEPT ![i] = "Try"]
    ELSE IF pc[i] = "Crit" THEN
      /\ pc' = [pc EXCEPT ![i] = "Exit"]
    ELSE
      /\ x' = 0
      /\ y' = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ S' = [S EXCEPT ![i] = {}]
      /\ pc' = [pc EXCEPT ![i] = "Start"]
    END

Spec ==
  Init /\ [][Next]_<<x, y, b, S, pc>>
 WF_<<x, y, b, S, pc>>(Next)

MutualExclusionInvariant ==
  \A i, j \in 1..N :
    pc[i] = "Crit" => pc[j] # "Crit"

LivenessProperty ==
  <>[]<>(\E i \in 1..N : pc[i] = "Crit")
```
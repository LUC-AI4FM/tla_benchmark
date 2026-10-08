------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N \* Number of processes, assumed to be >= 2

VARIABLES x, y, b, state, failed

Init == /\ x = 1
        /\ y = 0
        /\ b = [i \in 2..N -> FALSE]
        /\ state = [i \in 1..N -> "normal"]
        /\ failed = [i \in 1..N -> FALSE]

Next ==
    \/ /\ \/ /\ x > 1
             /\ y < x
             /\ \/ /\ state[1] = "try"
                    /\ \E i \in 2..N : b[i]
                \/ /\ state[1] = "cs"
                    /\ \A i \in 2..N : ~b[i]
             /\ x' = (CHOOSE z \in {y+1} \cup {k \in 1..N : k > y}: \A i \in 2..N : b[i] => z >= x)
             /\ y' = y
             /\ b' = [b EXCEPT ![x'] = TRUE]
             /\ state' = [state EXCEPT ![1] = "critical"]
             /\ failed' = failed
        \/ /\ state[1] = "normal"
            /\ x' = 1
            /\ y' = (CHOOSE z \in {0} \cup {k \in 1..N : k < x}: ~(\E i \in 2..N : b[i]))
            /\ b' = [b EXCEPT ![y'] = FALSE]
            /\ state' = [state EXCEPT ![1] = "try"]
            /\ failed' = failed
        \/ /\ state[1] = "critical"
            /\ x' = x
            /\ y' = y
            /\ b' = [b EXCEPT ![x] = FALSE]
            /\ state' = [state EXCEPT ![1] = "normal"]
            /\ failed' = failed
    \/ \E i \in 2..N :
         \/ /\ state[i] = "try"
              /\ x > 1
              /\ y < x
              /\ (\A j \in 2..N \ {i}: ~b[j])
              /\ x' = (CHOOSE z \in {y+1} \cup {k \in 1..N : k > y}: \A j \in 2..N: b[j] => z >= x)
              /\ y' = y
              /\ b' = [b EXCEPT ![x'] = TRUE]
              /\ state' = [state EXCEPT ![i] = "critical"]
              /\ failed' = failed
         \/ /\ state[i] = "normal"
              /\ x' = 1
              /\ y' = (CHOOSE z \in {0} \cup {k \in 1..N : k < x}: ~(\E j \in 2..N: b[j]))
              /\ b' = [b EXCEPT ![y'] = FALSE]
              /\ state' = [state EXCEPT ![i] = "try"]
              /\ failed' = failed
         \/ /\ state[i] = "critical"
              /\ x' = x
              /\ y' = y
              /\ b' = [b EXCEPT ![x] = FALSE]
              /\ state' = [state EXCEPT ![i] = "normal"]
              /\ failed' = failed

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b, state, failed>>
    /\ WF_[1]_<<x, y, b, state, failed>> (/\ state[1] = "try" \/ state[1] = "critical")
    /\ WF_{i \in 2..N}<<x, y, b, state, failed>>(/\ state[i] = "try" \/ state[i] = "critical")

MutualExclusion ==
    \A i, j \in 1..N : i # j => ~(\E k : (state[k] = "critical") /\ (i \in {1} \/ b[i]) /\ (j \in {1} \/ b[j]))

Liveness ==
    <>[] (\E i \in 1..N : state[i] = "critical")

THEOREM Spec => []MutualExclusion /\ Liveness
=============================================================================
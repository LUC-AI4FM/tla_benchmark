```
MODULE FastMutualExclusion
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES x, y, b, S, pc

Init == (* Initialize all variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ S = [i \in 1..N |-> {}]
        /\ pc = [i \in 1..N |-> "Start"]

Next == (* Next state relation *)
        \/ \E i \in 1..N :
            (* Label L1: test_and_set x *)
            (pc[i] = "L1" /\ x = 0
             /\ pc' = [pc EXCEPT ![i] = "L2"]
             /\ x' = 1
             /\ y' = i
             /\ b' = b
             /\ S' = S)
        \/ \E i \in 1..N :
            (* Label L2: test y *)
            (pc[i] = "L2" /\ y = i
             /\ pc' = [pc EXCEPT ![i] = "CS"]
             /\ x' = x
             /\ y' = y
             /\ b' = b
             /\ S' = S)
        \/ \E i \in 1..N :
            (* Label L2: retry *)
            (pc[i] = "L2" /\ y /= i
             /\ pc' = [pc EXCEPT ![i] = "Start"]
             /\ x' = x
             /\ y' = y
             /\ b' = b
             /\ S' = S)
        \/ \E i \in 1..N :
            (* Label CS: critical section *)
            (pc[i] = "CS"
             /\ pc' = [pc EXCEPT ![i] = "End"]
             /\ x' = x
             /\ y' = y
             /\ b' = b
             /\ S' = S)
        \/ \E i \in 1..N :
            (* Label End: reset *)
            (pc[i] = "End"
             /\ pc' = [pc EXCEPT ![i] = "Start"]
             /\ x' = 0
             /\ y' = 0
             /\ b' = [j \in 1..N |-> FALSE]
             /\ S' = [j \in 1..N |-> {}])

Spec == Init /\ [][Next]_<<x, y, b, S, pc>>
        /\ WF_vars(Next, <<x, y, b, S, pc>>)

MutualExclusionInv == (* Mutual exclusion invariant *)
        \A i, j \in 1..N :
            (pc[i] = "CS" /\ pc[j] = "CS") => i = j

Liveness == (* Liveness property: infinitely often some process is in CS *)
        <>[]\E i \in 1..N : pc[i] = "CS"

THEOREM Spec => []MutualExclusionInv
THEOREM Spec => Liveness
```
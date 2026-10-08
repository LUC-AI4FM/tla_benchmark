```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, S, pc

Init == (* Initial conditions *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ S = [i \in 1..N |-> {}]
        /\ pc = [i \in 1..N |-> "Start"]

Next == (* Next state relation *)
        \/ \E i \in 1..N :
            (pc[i] = "Start") /\ (x = 0) /\ 
            (y = 0) /\
            (b[i] = FALSE) /\
            (S[i] = {}) /\
            (pc' = [pc EXCEPT ![i] = "Retry1"]) /\ 
            (x' = i) /\ (y' = y) /\ (b' = b) /\ (S' = S)
        \/ \E i \in 1..N :
            (pc[i] = "Retry1") /\ (x = i) /\ (y = 0) /\
            (b[i] = FALSE) /\
            (S[i] = {}) /\
            (pc' = [pc EXCEPT ![i] = "Wait"]) /\ 
            (x' = x) /\ (y' = y) /\ (b' = b) /\ (S' = S)
        \/ \E i \in 1..N :
            (pc[i] = "Wait") /\ (x = i) /\ (y = 0) /\
            (b[i] = FALSE) /\
            (S[i] = {}) /\
            (pc' = [pc EXCEPT ![i] = "Critical"]) /\ 
            (x' = x) /\ (y' = y) /\ (b' = b) /\ (S' = S)
        \/ \E i \in 1..N :
            (pc[i] = "Critical") /\ (x = i) /\ (y = 0) /\
            (b[i] = FALSE) /\
            (S[i] = {}) /\
            (pc' = [pc EXCEPT ![i] = "End"]) /\ 
            (x' = x) /\ (y' = y) /\ (b' = b) /\ (S' = S)
        \/ \E i \in 1..N :
            (pc[i] = "End") /\ (x = i) /\ (y = 0) /\
            (b[i] = FALSE) /\
            (S[i] = {}) /\
            (pc' = [pc EXCEPT ![i] = "Start"]) /\ 
            (x' = x) /\ (y' = y) /\ (b' = b) /\ (S' = S)

MutualExclusion == (* Mutual exclusion invariant *)
        \A i, j \in 1..N : (pc[i] = "Critical") /\ (pc[j] = "Critical") => (i = j)

Spec == Init /\ [][Next]_<<x, y, b, S, pc>>
            /\ WF_<<x, y, b, S, pc>>(Next)
Liveness == (* Liveness property *)
        \A i \in 1..N : <>[]<>(pc[i] = "Critical")
THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
```
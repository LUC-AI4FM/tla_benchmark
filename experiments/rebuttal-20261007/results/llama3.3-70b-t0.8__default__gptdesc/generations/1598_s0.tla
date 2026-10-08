```
MODULE FastMutualExclusion
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N
VARIABLES x, y, b, S, pc

Init == (* Initialization condition *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ S = [i \in 1..N |-> {}]
        /\ pc = [i \in 1..N |-> "Start"]

Next == (* Next-state relation *)
        \E i \in 1..N :
          (pc[i] = "Start" /\ 
           b' = [b EXCEPT ![i] = TRUE] /\ 
           x' = i /\ 
           pc' = [pc EXCEPT ![i] = "Try1"]) \+
          (pc[i] = "Try1" /\ 
           y <> 0 /\ 
           b' = [b EXCEPT ![i] = FALSE] /\ 
           pc' = [pc EXCEPT ![i] = "Start"]) \+
          (pc[i] = "Try1" /\ 
           y = 0 /\ 
           y' = i /\ 
           pc' = [pc EXCEPT ![i] = "Try2"]) \+
          (pc[i] = "Try2" /\ 
           x = i /\ 
           S' = [S EXCEPT ![i] = {x}] /\ 
           pc' = [pc EXCEPT ![i] = "Wait1"]) \+
          (pc[i] = "Wait1" /\ 
           x \in S[i] /\ 
           b' = [b EXCEPT ![i] = FALSE] /\ 
           pc' = [pc EXCEPT ![i] = "Start"]) \+
          (pc[i] = "Wait1" /\ 
           x \notin S[i] /\ 
           pc' = [pc EXCEPT ![i] = "Crit"]) \+
          (pc[i] = "Crit" /\ 
           b' = [b EXCEPT ![i] = FALSE] /\ 
           y' = 0 /\ 
           pc' = [pc EXCEPT ![i] = "Start"])

Spec == Init /\ [][Next]_<<x, y, b, S, pc>>
            /\ WF_vars(Next, <<x, y, b, S, pc>>)

MutualExclusionInv == (* Mutual exclusion invariant *)
        \A i, j \in 1..N : 
          pc[i] = "Crit" /\ pc[j] = "Crit" => i = j

THEOREM Spec => []MutualExclusionInv
THEOREM Spec => <>[]\E i \in 1..N : pc[i] = "Crit"
```
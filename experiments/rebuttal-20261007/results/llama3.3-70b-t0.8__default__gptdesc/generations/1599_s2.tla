```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, pc

Init == (* Initial conditions *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "noncritical"]

Next == (* Next-state relation *)
        \/ \E i \in 1..N :
            (pc[i] = "noncritical" /\ pc' = [pc EXCEPT ![i] = "try"])
            \/ (pc[i] = "try" /\ x = 0 /\ b' = [b EXCEPT ![i] = TRUE] /\ pc' = [pc EXCEPT ![i] = "waitingX"])
            \/ (pc[i] = "waitingX" /\ x = i /\ y = 0 /\ b' = b /\ pc' = [pc EXCEPT ![i] = "waitingY"])
            \/ (pc[i] = "waitingY" /\ y = i /\ b' = b /\ pc' = [pc EXCEPT ![i] = "critical"])
            \/ (pc[i] = "critical" /\ b' = b /\ pc' = [pc EXCEPT ![i] = "exit"])
            \/ (pc[i] = "exit" /\ b' = [b EXCEPT ![i] = FALSE] /\ pc' = [pc EXCEPT ![i] = "noncritical"])

Spec == (* Specification *)
        Init /\ [][Next]_<<x, y, b, pc>>

MutualExclusion == (* Safety invariant: Mutual exclusion *)
        \A i, j \in 1..N : i # j => ~(pc[i] = "critical" /\ pc[j] = "critical")

Liveness == (* Liveness property *)
        \A i \in 1..N : <>[]<>(pc[i] = "critical")

ConditionalLiveness == (* Conditional liveness property *)
        \A i \in 1..N : []<>((pc[i] = "try") => <>(pc[i] = "critical"))

Fairness == (* Weak fairness for each control-location action *)
        \A i \in 1..N :
            WF_vars(<<x, y, b, pc>>, "try", i) /\
            WF_vars(<<x, y, b, pc>>, "waitingX", i) /\
            WF_vars(<<x, y, b, pc>>, "waitingY", i) /\
            WF_vars(<<x, y, b, pc>>, "critical", i) /\
            WF_vars(<<x, y, b, pc>>, "exit", i)

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
THEOREM Spec => ConditionalLiveness
THEOREM Spec => Fairness
```
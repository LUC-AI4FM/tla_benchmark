```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, pc

Init == (* Initial condition *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "noncritical"]

Next == (* Next-state relation *)
        \/ \E i \in 1..N :
            (pc[i] = "noncritical" /\ NextNoncritical(i))
        \/ \E i \in 1..N :
            (pc[i] = "try" /\ NextTry(i))
        \/ \E i \in 1..N :
            (pc[i] = "wait" /\ NextWait(i))
        \/ \E i \in 1..N :
            (pc[i] = "critical" /\ NextCritical(i))
        \/ \E i \in 1..N :
            (pc[i] = "exit" /\ NextExit(i))

NextNoncritical(i) == (* Noncritical section *)
        pc' = [pc EXCEPT ![i] = "try"]

NextTry(i) == (* Try to enter critical section *)
        /\ x' = i
        /\ b' = [b EXCEPT ![i] = TRUE]
        /\ pc' = [pc EXCEPT ![i] = "wait"]
        /\ y' = IF y = 0 THEN i ELSE y

NextWait(i) == (* Wait for critical section *)
        /\ (y = i /\ x' = 0 /\ b' = [b EXCEPT ![i] = FALSE] /\ pc' = [pc EXCEPT ![i] = "critical"])
        \/ (y /= i /\ pc' = pc)

NextCritical(i) == (* Critical section *)
        /\ pc' = [pc EXCEPT ![i] = "exit"]

NextExit(i) == (* Exit critical section *)
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ y' = 0
        /\ x' = 0
        /\ pc' = [pc EXCEPT ![i] = "noncritical"]

Spec == (* Specification *)
        Init /\ [][Next]_<<x, y, b, pc>>

MutualExclusion == (* Mutual exclusion safety invariant *)
        \A i, j \in 1..N : i /= j => ~(pc[i] = "critical" /\ pc[j] = "critical")

THEOREM Spec => []MutualExclusion

Fairness == (* Weak fairness for each control-location action except noncritical-section and critical-section skip steps *)
        \A i \in 1..N :
            WF_vars(NextNoncritical(i), <<x, y, b, pc>>)
        /\ WF_vars(NextTry(i), <<x, y, b, pc>>)
        /\ WF_vars(NextWait(i), <<x, y, b, pc>>)
        /\ WF_vars(NextExit(i), <<x, y, b, pc>>)

SpecFair == (* Fairness-enhanced specification *)
        Spec /\ Fairness
```
---------------------------- MODULE FastMutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, b, S, pc

Init == (* Initial conditions *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ S = [i \in 1..N |-> {}]
        /\ pc = [i \in 1..N |-> "Start"]

Next == (* Next-state relation *)
        \E i \in 1..N :
          IF pc[i] = "Start" THEN
            (* Label Start: try to enter critical section *)
            /\ x' = i
            /\ UNCHANGED <<y, b, S, pc>>
          ELSE IF pc[i] = "Retry" THEN
            (* Label Retry: retry entering critical section *)
            /\ y' = i
            /\ b' = [b EXCEPT ![i] = TRUE]
            /\ UNCHANGED <<x, S, pc>>
          ELSE IF pc[i] = "Wait" THEN
            (* Label Wait: wait for other process to exit *)
            /\ S' = [S EXCEPT ![i] = S[i] \cup {y}]
            /\ UNCHANGED <<x, y, b, pc>>
          ELSE IF pc[i] = "CS" THEN
            (* Label CS: in critical section *)
            /\ pc' = [pc EXCEPT ![i] = "Exit"]
            /\ UNCHANGED <<x, y, b, S>>
          ELSE IF pc[i] = "Exit" THEN
            (* Label Exit: exit critical section *)
            /\ x' = 0
            /\ y' = 0
            /\ b' = [b EXCEPT ![i] = FALSE]
            /\ S' = [S EXCEPT ![i] = {}]
            /\ pc' = [pc EXCEPT ![i] = "Start"]
          ELSE
            (* Should not happen *)
            /\ UNCHANGED <<x, y, b, S, pc>>

Spec == Init /\ [][Next]_<<x, y, b, S, pc>>
WeakFairness == WF_vars(Next, <<x, y, b, S, pc>>)

Invariant == (* Mutual exclusion invariant *)
             \A i, j \in 1..N : i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")

Liveness == (* Liveness property: infinitely often some process is in CS *)
            <>[](\E i \in 1..N : pc[i] = "CS")
=============================================================================
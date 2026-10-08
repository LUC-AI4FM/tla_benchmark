```
MODULE LockProtocol
EXTENDS Integers, TLC
CONSTANTS NumProcs
VARIABLES h_turn, s, turn, pc

Init == (* Initial state *)
        /\ h_turn = << >> 
        /\ s = 0
        /\ turn = 1
        /\ pc = [i \in 1..NumProcs |-> "N"]

Next == (* Transition relation *)
        \/ (* Entry protocol step 1: request to enter critical section *)
           \E i \in 1..NumProcs :
             pc[i] = "N" /\ pc' = [pc EXCEPT ![i] = "T1"]
           \/ (* Entry protocol step 2: set turn variable *)
           \E i \in 1..NumProcs :
             pc[i] = "T1" /\ turn' = i /\ h_turn' = Append(h_turn, i) /\ pc' = [pc EXCEPT ![i] = "T2"]
           \/ (* Entry protocol step 3: enter critical section *)
           \E i \in 1..NumProcs :
             pc[i] = "T2" /\ turn = i /\ pc' = [pc EXCEPT ![i] = "C"] /\ s' = s + 1
           \/ (* Exit critical section *)
           \E i \in 1..NumProcs :
             pc[i] = "C" /\ pc' = [pc EXCEPT ![i] = "N"]
           \/ (* Stuttering step *)
             pc' = pc /\ turn' = turn /\ h_turn' = h_turn /\ s' = s + 1

Spec == Init /\ [][Next]_<<h_turn, s, turn, pc>>

THEOREM Spec => []pc["C"] = << >>
```
Note: The Peterson specification and Stuttering module are not included in this code as they were not provided. This code only includes the LockProtocol module.
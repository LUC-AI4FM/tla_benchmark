```
MODULE BakeryAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs
VARIABLES tickets, choosing, readSet, max, nextExamined, pc

Init == (* Initial conditions *)
        /\ tickets = [i \in 1..NumProcs |-> 0]
        /\ choosing = [i \in 1..NumProcs |-> FALSE]
        /\ readSet = [i \in 1..NumProcs |-> {}]
        /\ max = 0
        /\ nextExamined = 1
        /\ pc = [i \in 1..NumProcs |-> "NCS"]


Next == (* Next state relation *)
        \/ \E i \in 1..NumProcs :
            (pc[i] = "NCS") /\ choosing[i] = FALSE
            /\ tickets[i] < max
            /\ pc' = [pc EXCEPT ![i] = "TRY"]
            /\ tickets' = tickets
            /\ choosing' = [choosing EXCEPT ![i] = TRUE]
            /\ readSet' = readSet
            /\ max' = max
            /\ nextExamined' = nextExamined
        \/ \E i \in 1..NumProcs :
            (pc[i] = "TRY") /\ choosing[i] = TRUE
            /\ tickets[i] = 0
            /\ pc' = [pc EXCEPT ![i] = "CS"]
            /\ tickets' = [tickets EXCEPT ![i] = max + 1]
            /\ choosing' = [choosing EXCEPT ![i] = FALSE]
            /\ readSet' = [readSet EXCEPT ![i] = {j \in 1..NumProcs : tickets[j] # 0}]
            /\ max' = max + 1
            /\ nextExamined' = 1
        \/ \E i \in 1..NumProcs :
            (pc[i] = "CS") /\ choosing[i] = FALSE
            /\ tickets[i] > max
            /\ pc' = [pc EXCEPT ![i] = "NCS"]
            /\ tickets' = tickets
            /\ choosing' = choosing
            /\ readSet' = readSet
            /\ max' = max
            /\ nextExamined' = nextExamined + 1


Spec == Init /\ [][Next]_<<tickets, choosing, readSet, max, nextExamined, pc>>


THEOREM Spec => []<>(\E i \in 1..NumProcs : pc[i] = "CS")
INVARIANT (MaxTickets == max)
ASSUME NumProcs > 0
```
Note: The above TLA+ code models Lamport's Bakery algorithm for mutual exclusion. It defines the initial state and the next-state relation, as well as the specification of the system. Additionally, it includes a theorem stating that the system will eventually have at least one process in the critical section and an invariant bounding ticket values.

To ensure safety property (mutual exclusion), add the following:
```
MutualExclusion == []<>(\A i, j \in 1..NumProcs : 
                    pc[i] = "CS" /\ pc[j] = "CS" => i = j)
THEOREM Spec => MutualExclusion
```
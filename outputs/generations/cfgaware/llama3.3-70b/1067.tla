---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Node

VARIABLE active, detected

Init == (* Initial state: all nodes are inactive, detection flag is off *)
        /\ active = {}
        /\ detected = FALSE

TypeInvariant == (* Type invariant: active is a subset of Node *)
                 active \subseteq Node

Next == (* Next-state relation: either an active node terminates, 
           an active node wakes up another node, or the detection step occurs *)
         \/ \E n \in active : (* Active node terminates *)
               active' = active \ {n}
               /\ detected' = detected
         \/ \E n \in active \* m \in Node : (* Active node wakes up another node *)
               active' = active \cup {m}
               /\ detected' = detected
         \/ (* Detection step: set detection flag when all nodes are inactive *)
               active' = active
               /\ detected' = ~active = {}

Spec == Init /\ [][Next]_<<active, detected>>
        
Fairness == (* Fairness condition on the detection action *)
            <>(~active = {}) => <>detected

Correctness == (* Correctness property: if all nodes are inactive, 
                 then the detection flag will be set eventually *)
               [](~active = {} => <>detected)

Quiescence == (* Quiescence property: if no node is active and the detection flag is off, 
                then no action can occur *)
              [](~active = {} /\ ~detected => Next)

Liveness == (* Liveness property: if a node becomes active, 
               it will eventually terminate or wake up another node *)
             []<n \in Node : <>~(n \in active)>

THEOREM Spec => []TypeInvariant
THEOREM Spec => Correctness
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
====================================================================================
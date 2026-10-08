```
MODULE Bakery
EXTENDS Integers

CONSTANTS NumProcs, MaxTicket

VARIABLES pc, ticket, entering

Init ==
  /\ pc = [i \in 1..NumProcs |-> "NCS"]  -- all processes in non-critical section initially
  /\ ticket = [i \in 1..NumProcs |-> 0]  -- initialize tickets to 0
  /\ entering = [i \in 1..NumProcs |-> FALSE]

Next ==
  /\ \E i \in 1..NumProcs :
     /\ pc[i] = "NCS"
     /\ ticket[i] = 0
     /\ entering' = [entering EXCEPT ![i] = TRUE]
     /\ pc' = [pc EXCEPT ![i] = "TRY"]
     /\ ticket' = [ticket EXCEPT ![i] = 1 + CHOOSE j \in 1..NumProcs : ticket[j]]
  \/ \E i \in 1..NumProcs :
     /\ pc[i] = "TRY"
     /\ entering[i]
     /\ \A j \in 1..NumProcs : 
        (ticket[j] # 0) => (ticket[i] < ticket[j])
     /\ pc' = [pc EXCEPT ![i] = "CS"]
     /\ entering' = [entering EXCEPT ![i] = FALSE]
     /\ ticket' = ticket
  \/ \E i \in 1..NumProcs :
     /\ pc[i] = "CS"
     /\ entering[i] = FALSE
     /\ pc' = [pc EXCEPT ![i] = "NCS"]
     /\ entering' = entering
     /\ ticket' = ticket

Spec == Init /\ [][Next]_<<pc, ticket, entering>>
           /\ WF_<<pc, ticket, entering>>(Next)

THEOREM Spec => []~( \E i, j \in 1..NumProcs : 
                    (i # j) /\ pc[i] = "CS" /\ pc[j] = "CS")
THEOREM Spec => <>[]pc[1] = "CS"
CONSTRAINT ticket \in [1..NumProcs -> 0..MaxTicket]
```
Note that the `CHOOSE` operator used in this specification will be evaluated by TLC during model checking. For a more efficient evaluation, consider using `Min` or `Max` with an empty set if no suitable value is found. 

To use this module in TLC, define `NumProcs` and `MaxTicket` in the model's configuration file as constants of type integer, for example: 
```
 NumProcs = 3
 MaxTicket = 10
```
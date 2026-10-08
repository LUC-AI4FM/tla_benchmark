```
MODULE Bakery
EXTENDS Integers

CONSTANTS NumProcs, MaxTicket

VARIABLES state, ticket, aux

state == [i \in 1..NumProcs |-> "NonCritical"]
ticket == [i \in 1..NumProcs |-> 0]
aux == << >>

Init ==
  /\ state = [i \in 1..NumProcs |-> "NonCritical"]
  /\ ticket = [i \in 1..NumProcs |-> 0]
  /\ aux = << >>

Next ==
  (\E i \in 1..NumProcs :
    /\ state[i] = "NonCritical"
    /\ ticket[i] = 0
    /\ state' = [state EXCEPT ![i] = "Trying"]
    /\ ticket' = [ticket EXCEPT ![i] = (1 + CHOOSE j \in 1..NumProcs : ticket[j] > ticket[i])]
    /\ aux' = << i >> @ aux
  )
  \/
  (\E i \in 1..NumProcs :
    /\ state[i] = "Trying"
    /\ (\A j \in 1..NumProcs : j # i => (ticket[i] < ticket[j]) \/ (ticket[i] = ticket[j] /\ i < j))
    /\ state' = [state EXCEPT ![i] = "Critical"]
    /\ ticket' = ticket
    /\ aux' = << i >> @ aux
  )
  \/
  (\E i \in 1..NumProcs :
    /\ state[i] = "Critical"
    /\ state' = [state EXCEPT ![i] = "NonCritical"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ aux' = << >>
  )

Spec ==
  Init /\ [][Next]_<<state, ticket, aux>>

MutualExclusion == \A i, j \in 1..NumProcs : ~ (state[i] = "Critical" /\ state[j] = "Critical")
TypeInvariant == state \in [1..NumProcs -> {"NonCritical", "Trying", "Critical"}]
TicketInvariant == ticket \in [1..NumProcs -> 0..MaxTicket]

THEOREM Spec => []MutualExclusion
THEOREM Spec => []TypeInvariant
THEOREM Spec => []TicketInvariant

FAIRNESS STATE state
```
Note: To verify this specification with TLC, you will need to set the model parameters `NumProcs` and `MaxTicket` to specific values.
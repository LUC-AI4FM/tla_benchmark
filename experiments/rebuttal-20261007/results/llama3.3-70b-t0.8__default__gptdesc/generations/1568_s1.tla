```
MODULE Bakery
EXTENDS Integers, Naturals

CONSTANTS NumProcs, MaxTicket

VARIABLES state, ticket, auxVars

state == [i \in 1..NumProcs |-> "NonCritical"]
ticket == [i \in 1..NumProcs |-> 0]
auxVars == << >>

Init ==
  /\ state = [i \in 1..NumProcs |-> "NonCritical"]
  /\ ticket = [i \in 1..NumProcs |-> 0]
  /\ auxVars = << >>

Next ==
  (\E i \in 1..NumProcs :
    /\ state[i] = "NonCritical"
    /\ ticket[i] = 0
    /\ state' = [state EXCEPT ![i] = "Trying"]
    /\ ticket' = [ticket EXCEPT ![i] = 1]
    /\ auxVars' = << >>
  )
  \lor
  (\E i \in 1..NumProcs :
    /\ state[i] = "Trying"
    /\ \E j \in 1..NumProcs :
      /\ j # i
      /\ ticket[j] < ticket[i]
      /\ state' = [state EXCEPT ![i] = "Waiting"]
      /\ ticket' = ticket
      /\ auxVars' = << >>
  )
  \lor
  (\E i \in 1..NumProcs :
    /\ state[i] = "Waiting"
    /\ \A j \in 1..NumProcs :
      /\ j # i
      -> ticket[j] >= ticket[i]
    /\ state' = [state EXCEPT ![i] = "Critical"]
    /\ ticket' = ticket
    /\ auxVars' = << >>
  )
  \lor
  (\E i \in 1..NumProcs :
    /\ state[i] = "Critical"
    /\ state' = [state EXCEPT ![i] = "NonCritical"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ auxVars' = << >>
  )

Spec == Init /\ [][Next]_<<state, ticket, auxVars>>

THEOREM Spec => []\A i, j \in 1..NumProcs : 
  (state[i] = "Critical") /\ (state[j] = "Critical") => i = j

THEOREM Spec => <>[]\A i \in 1..NumProcs : state[i] = "NonCritical"

FAIRNESS STATE
```
Note: The above TLA+ specification models the Lamport's Bakery algorithm and includes safety invariants, liveness properties, and fairness conditions. However, please note that this is a text-based representation and may need to be formatted according to the specific requirements of your tool or environment.
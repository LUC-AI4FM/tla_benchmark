```
MODULE BakeryAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs, MaxTicket

VARIABLES state, ticket, auxVars

Init ==
  /\ state = [i \in 1..NumProcs |-> "NonCritical"]
  /\ ticket = [i \in 1..NumProcs |-> 0]
  /\ auxVars = [i \in 1..NumProcs |-> FALSE]

Next ==
  /\ IF \E i \in 1..NumProcs :
        /\ state[i] = "NonCritical"
        /\ ticket[i] = 0
        /\ auxVars[i] = FALSE
        THEN
          /\ state' = [state EXCEPT ![i] = "Waiting"]
          /\ ticket' = [ticket EXCEPT ![i] = (CHOOSE m \in Nat : m > 0)]
          /\ auxVars' = [auxVars EXCEPT ![i] = TRUE]
          ELSE
            IF \E i \in 1..NumProcs :
              /\ state[i] = "Waiting"
              /\ \A j \in 1..NumProcs : j # i => (state[j] = "NonCritical" \/ ticket[j] > ticket[i])
              THEN
                /\ state' = [state EXCEPT ![i] = "Critical"]
                /\ ticket' = ticket
                /\ auxVars' = auxVars
              ELSE
                IF \E i \in 1..NumProcs :
                  /\ state[i] = "Critical"
                  /\ auxVars[i] = TRUE
                THEN
                  /\ state' = [state EXCEPT ![i] = "NonCritical"]
                  /\ ticket' = [ticket EXCEPT ![i] = 0]
                  /\ auxVars' = [auxVars EXCEPT ![i] = FALSE]
                ELSE
                  /\ state' = state
                  /\ ticket' = ticket
                  /\ auxVars' = auxVars

Spec ==
  Init /\ [][Next]_state /\ [][Next]_ticket /\ [][Next]_auxVars

MutualExclusion == <>[]~( \E i, j \in 1..NumProcs : i # j /\ state[i] = "Critical" /\ state[j] = "Critical" )

THEOREM Spec => []MutualExclusion

Fairness ==
  WF_Vars(Next, state) /\ WF_Vars(Next, ticket) /\ WF_Vars(Next, auxVars)

CONSTRAINT MaxTicketConstraint == MaxTicket = 1000
```
Note: The model uses the `CHOOSE` operator to assign a unique positive integer value to each process's ticket. In practice, this would typically be implemented using a more sophisticated method to ensure uniqueness and fairness. Additionally, the specification includes an arbitrary constraint (`MaxTicketConstraint`) for TLC model checking purposes; in reality, this value should be chosen based on the specific requirements of the system being modeled.
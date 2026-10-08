---- MODULE BakeryAlgorithm ----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumProcesses, MaxTicketValue

VARIABLES 
    state \in [1..NumProcesses -> {"idle", "waiting", "held"}],
    ticket \in [1..NumProcesses -> 0..MaxTicketValue]

Init == /\ state = [p \in 1..NumProcesses |-> "idle"]
        /\ ticket = [p \in 1..NumProcesses |-> 0]

ChooseMax ==
    {max \in Nat : \A p \in 1..NumProcesses : ticket[p] <= max}

Next ==
    \/ \E p, t \in 1..NumProcesses :
       /\ state[p] = "idle"
       /\ ticket' = [ticket EXCEPT ![p] = ChooseMax]
       /\ state' = [state EXCEPT ![p] = "waiting"]
   \/ \E p \in 1..NumProcesses :
      /\ state[p] = "waiting"
      /\ (\A q \in {q \in 1..NumProcesses : ticket[q] /= 0} :
            (ticket[q] > ticket[p]) \/
            (ticket[q] = ticket[p] /\ q < p))
      /\ state' = [state EXCEPT ![p] = "held"]
   \/ \E p \in 1..NumProcesses :
      /\ state[p] = "held"
      /\ state' = [state EXCEPT ![p] = "idle"]
      /\ ticket' = [ticket EXCEPT ![p] = 0]

Spec ==
    /\ Init
    /\ [][Next]_<<state, ticket>>
    /\ WF_next(<<state, ticket>>)

MaxTicketConstraint == 
    \A p \in 1..NumProcesses : ticket[p] <= MaxTicketValue

MutualExclusion ==
    \/ state[p] # "held" \/ \A q \in {q \in 1..NumProcesses : q /= p} : state[q] # "held"

Invariant ==
    /\ MutualExclusion
    /\ MaxTicketConstraint

THEOREM Spec => []Invariant
====
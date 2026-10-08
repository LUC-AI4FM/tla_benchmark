------------------------------- MODULE BakeryAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcesses, MaxTicketValue

VARIABLES 
    state \in [1..NumProcesses -> {"idle", "waiting", "critical"}],
    ticket \in [1..NumProcesses -> 0..MaxTicketValue],
    choosing \in [1..NumProcesses -> BOOLEAN]

Init == 
    /\ \/ state = [p \in 1..NumProcesses |-> "idle"]
    /\ \/ ticket = [p \in 1..NumProcesses |-> 0]
    /\ \/ choosing = [p \in 1..NumProcesses |-> FALSE]

ChooseTicket ==
    /\ \/ \E p \in 1..NumProcesses : state[p] = "waiting" /\ ~choosing[p]
    /\ \/ \E p \in 1..NumProcesses : state[p] = "waiting" /\ ~choosing[p] => choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ \/ \E p \in 1..NumProcesses : state[p] = "waiting" /\ ~choosing[p] => ticket' = [ticket EXCEPT ![p] = Max(\{ticket[q] : q \in 1..NumProcesses}) + 1]

EnterCritical ==
    /\ \/ \E p \in 1..NumProcesses : state[p] = "waiting" /\ choosing[p]
    /\ \/ \A q \in (1..NumProcesses) \ {p} : ticket[q] < ticket[p] \/ (ticket[q] = ticket[p] /\ q < p)
    /\ \/ state' = [state EXCEPT ![p] = "critical"]
    /\ \/ choosing' = [choosing EXCEPT ![p] = FALSE]

ExitCritical ==
    /\ \/ \E p \in 1..NumProcesses : state[p] = "critical"
    /\ \/ state' = [state EXCEPT ![p] = "idle"]
    /\ \/ ticket' = [ticket EXCEPT ![p] = 0]

Next == 
    \/ \E p \in 1..NumProcesses : state[p] = "idle" /\ state' = [state EXCEPT ![p] = "waiting"]
    \/ ChooseTicket
    \/ EnterCritical
    \/ ExitCritical

Spec == Init /\ [][Next]_<<state, ticket, choosing>>

(* Fairness conditions *)
WFState == WF_next(state)
WFChoosing == WF_next(choosing)

MutualExclusion ==
    \A p, q \in 1..NumProcesses : p # q => ~(\E i \in 0..MaxTicketValue : state[p] = "critical" /\ ticket[p] = i /\ state[q] = "critical" /\ ticket[q] = i)

Properties == 
    /\ MutualExclusion

THEOREM Spec => []Properties
================================================================================
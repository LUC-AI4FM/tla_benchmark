------------------------------ MODULE BakeryMutex ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NumProcesses \* Number of processes

VARIABLES 
    choosing,             \* Set of processes currently choosing tickets
    nextNumber,           \* Next available ticket number
    numbers,              \* Array of ticket numbers assigned to each process
    inCS,                 \* Set of processes currently in the critical section
    localReads            \* Local read sets for each process

ASSUME NumProcesses \in Nat /\ NumProcesses > 0

Init == 
    /\ choosing = {}
    /\ nextNumber = 1
    /\ numbers = [p \in 1..NumProcesses -> 0]
    /\ inCS = {}
    /\ localReads = [p \in 1..NumProcesses -> {}]

Next ==
    \/ \E p \in (1..NumProcesses) \ {pc} :
        \/ \/ \* Phase 1: Choosing a ticket
               choosing' = choosing \cup {p}
           /\ numbers' = [numbers EXCEPT ![p] = nextNumber]
           /\ nextNumber' = nextNumber + 1
           /\ UNCHANGED <<inCS, localReads>>
        \/ \/ \* Phase 2: Determining the order and waiting for others
               choosing' = choosing \ {p}
           /\ localReads' = [localReads EXCEPT ![p] = (numbers \cap {(n, q) \in numbers : n >= numbers[p]})]
           /\ UNCHANGED <<nextNumber, inCS>>
        \/ \/ \* Phase 3: Entering the critical section
               localReads[p] = {<numbers[p], p>}
           /\ inCS' = inCS \cup {p}
           /\ UNCHANGED <<choosing, nextNumber, numbers>>
        \/ \/ \* Exiting the critical section
               inCS' = inCS \ {p}
           /\ numbers' = [numbers EXCEPT ![p] = 0]
           /\ UNCHANGED <<choosing, nextNumber, localReads>>

Spec == 
    Init /\ [][Next]_<<choosing, nextNumber, numbers, inCS, localReads>> /\ WF_[Next]_<<choosing, nextNumber, numbers, inCS, localReads>>

\* Safety properties
InvariantMutualExclusion ==
    \A p1, p2 \in 1..NumProcesses :
        \/ p1 = p2
        \/ \/ ~(p1 \in inCS) 
           \/ ~(p2 \in inCS)

StateConstraintTickets ==
    \A p \in 1..NumProcesses : numbers[p] \leq nextNumber

\* Liveness properties
LiveProgress ==
    \A p \in 1..NumProcesses :
        <>(~(choosing[p]) /\ localReads[p] = {<numbers[p], p>} /\ ~(p \in inCS))

=============================================================================
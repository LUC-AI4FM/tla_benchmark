---------------------------- MODULE PrisonerLamp ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N, KnownOff

VARIABLES lamp, counter, signaled, visited, declared, turn

vars == <<lamp, counter, signaled, visited, declared, turn>>

Prisoners == 1..N

CounterPrisoner == 1

NonCounterPrisoners == 2..N

Threshold == IF KnownOff THEN N ELSE 2*N - 1

MaxSignals == IF KnownOff THEN 1 ELSE 2

TypeOK ==
    /\ lamp \in BOOLEAN
    /\ counter \in 0..Threshold
    /\ signaled \in [NonCounterPrisoners -> 0..MaxSignals]
    /\ visited \in SUBSET Prisoners
    /\ declared \in BOOLEAN
    /\ turn \in Prisoners \cup {0}

Init ==
    /\ lamp = IF KnownOff THEN FALSE ELSE FALSE
    /\ counter = 0
    /\ signaled = [p \in NonCounterPrisoners |-> 0]
    /\ visited = {}
    /\ declared = FALSE
    /\ turn = 0

SelectPrisoner(p) ==
    /\ ~declared
    /\ turn = 0
    /\ turn' = p
    /\ UNCHANGED <<lamp, counter, signaled, visited, declared>>

CounterVisit ==
    /\ ~declared
    /\ turn = CounterPrisoner
    /\ visited' = visited \cup {CounterPrisoner}
    /\ IF lamp = TRUE
       THEN /\ counter' = counter + 1
            /\ lamp' = FALSE
            /\ IF counter + 1 >= Threshold
               THEN declared' = TRUE
               ELSE declared' = FALSE
       ELSE /\ counter' = counter
            /\ lamp' = lamp
            /\ declared' = FALSE
    /\ UNCHANGED signaled
    /\ turn' = 0

NonCounterVisit(p) ==
    /\ ~declared
    /\ turn = p
    /\ p \in NonCounterPrisoners
    /\ visited' = visited \cup {p}
    /\ IF lamp = FALSE /\ signaled[p] < MaxSignals
       THEN /\ lamp' = TRUE
            /\ signaled' = [signaled EXCEPT ![p] = signaled[p] + 1]
       ELSE /\ lamp' = lamp
            /\ signaled' = signaled
    /\ UNCHANGED <<counter, declared>>
    /\ turn' = 0

Next ==
    \/ \E p \in Prisoners : SelectPrisoner(p)
    \/ CounterVisit
    \/ \E p \in NonCounterPrisoners : NonCounterVisit(p)

Fairness ==
    /\ \A p \in Prisoners : WF_vars(SelectPrisoner(p))
    /\ WF_vars(CounterVisit)
    /\ \A p \in NonCounterPrisoners : WF_vars(NonCounterVisit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Terminating == declared

VictoryOK == declared => (visited = Prisoners)

Safety == [](declared => (visited = Prisoners))

AllVisited == visited = Prisoners

Liveness == <>(declared /\ AllVisited)

=============================================================================
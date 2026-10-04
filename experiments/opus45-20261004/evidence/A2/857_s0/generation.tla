---------------------------- MODULE PrisonerPuzzle ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Prisoner, Light_Unknown

VARIABLES counter_count, victory_announced, signalled, lamp_on, visited

vars == <<counter_count, victory_announced, signalled, lamp_on, visited>>

N == Cardinality(Prisoner)

Counter == CHOOSE p \in Prisoner : TRUE

NonCounters == Prisoner \ {Counter}

MaxSignals == IF Light_Unknown THEN 2 ELSE 1

VictoryThreshold == IF Light_Unknown THEN 2 * N - 1 ELSE N

TypeOK ==
    /\ counter_count \in 1..VictoryThreshold
    /\ victory_announced \in BOOLEAN
    /\ signalled \in [NonCounters -> 0..MaxSignals]
    /\ lamp_on \in BOOLEAN
    /\ visited \in SUBSET Prisoner

Init ==
    /\ counter_count = 1
    /\ victory_announced = FALSE
    /\ signalled = [p \in NonCounters |-> 0]
    /\ lamp_on \in IF Light_Unknown THEN BOOLEAN ELSE {FALSE}
    /\ visited = {}

CounterVisit ==
    /\ ~victory_announced
    /\ visited' = visited \cup {Counter}
    /\ IF lamp_on
       THEN /\ lamp_on' = FALSE
            /\ counter_count' = counter_count + 1
            /\ IF counter_count + 1 = VictoryThreshold
               THEN victory_announced' = TRUE
               ELSE victory_announced' = FALSE
       ELSE /\ lamp_on' = lamp_on
            /\ counter_count' = counter_count
            /\ victory_announced' = FALSE
    /\ UNCHANGED signalled

NonCounterVisit(p) ==
    /\ p \in NonCounters
    /\ ~victory_announced
    /\ visited' = visited \cup {p}
    /\ IF ~lamp_on /\ signalled[p] < MaxSignals
       THEN /\ lamp_on' = TRUE
            /\ signalled' = [signalled EXCEPT ![p] = signalled[p] + 1]
       ELSE /\ lamp_on' = lamp_on
            /\ signalled' = signalled
    /\ UNCHANGED <<counter_count, victory_announced>>

WardenSelectsCounter ==
    CounterVisit

WardenSelectsNonCounter(p) ==
    NonCounterVisit(p)

Next ==
    \/ WardenSelectsCounter
    \/ \E p \in NonCounters : WardenSelectsNonCounter(p)

Fairness ==
    /\ WF_vars(WardenSelectsCounter)
    /\ \A p \in NonCounters : WF_vars(WardenSelectsNonCounter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

VictoryOK ==
    victory_announced => (visited = Prisoner)

Terminating == <>(victory_announced)

=============================================================================
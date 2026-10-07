------------------------------- MODULE PrisonersAndSwitches -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Prisoner, Counter
ASSUME Cardinality(Prisoner) >= 2 /\ Counter \in Prisoner

VARIABLES switchAUp, switchBUp, timesSwitched, count, Done

Init == 
    /\ switchAUp \in {TRUE, FALSE}
    /\ switchBUp \in {TRUE, FALSE}
    /\ timesSwitched \in [Prisoner \ {Counter} -> {0, 1, 2}]
    /\ count = 0
    /\ Done = FALSE

Next ==
    LET prisoner = CHOOSE p \in Prisoner : TRUE
        nextTimesSwitched == 
            IF prisoner = Counter THEN timesSwitched
            ELSE [timesSwitched EXCEPT ![prisoner] = (IF switchAUp & timesSwitched[prisoner] < 2 THEN timesSwitched[prisoner] + 1 ELSE timesSwitched[prisoner])]
        nextCount ==
            IF prisoner = Counter & switchAUp THEN count + 1
            ELSE count
        nextSwitchAUp ==
            IF prisoner = Counter & switchAUp THEN FALSE
            ELSE IF prisoner \in Prisoner \ {Counter} & ~switchAUp & timesSwitched[prisoner] < 2 THEN TRUE
            ELSE switchAUp
        nextSwitchBUp ==
            IF prisoner = Counter & ~switchAUp THEN ~switchBUp
            ELSE IF prisoner \in Prisoner \ {Counter} & (switchAUp \/ timesSwitched[prisoner] >= 2) THEN ~switchBUp
            ELSE switchBUp
    IN
        /\ switchAUp' = nextSwitchAUp
        /\ switchBUp' = nextSwitchBUp
        /\ timesSwitched' = nextTimesSwitched
        /\ count' = nextCount
        /\ Done' = (count' >= 2 * (Cardinality(Prisoner) - 1))

Spec ==
    /\ Init
    /\ [][Next]_<<switchAUp, switchBUp, timesSwitched, count, Done>>
    /\ WF_<<prisoners>>[Next]

CountInvariant ==
    \/ ~switchAUp /\ count = \E p \in Prisoner \ {Counter} : timesSwitched[p]
    \/  switchAUp /\ count + 1 = \E p \in Prisoner \ {Counter} : timesSwitched[p]

Safety ==
    Done => (\A p \in Prisoner \ {Counter} : timesSwitched[p] >= 1)

Liveness ==
    <>Done

TypeOK ==
    /\ switchAUp \in BOOLEAN
    /\ switchBUp \in BOOLEAN
    /\ timesSwitched \in [Prisoner \ {Counter} -> {0, 1, 2}]
    /\ count \in 0..(2 * Cardinality(Prisoner) - 1)
    /\ Done \in BOOLEAN

================================================================================
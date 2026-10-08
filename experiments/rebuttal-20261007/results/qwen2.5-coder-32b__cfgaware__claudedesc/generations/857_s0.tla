---- MODULE PrisonerPuzzle ----

CONSTANTS Prisoner, Light_Unknown

VARIABLES count, victoryAnnounced, prisonerSignals, lampState, wardenRecord

N == Cardinality(Prisoner)
Counter == CHOOSE p \in Prisoner : TRUE  \* Arbitrarily choose one prisoner as the counter
NonCounters == Prisoner \ {Counter}

Spec ==
    /\ TYPEOK
    /\ Init
    /\ [][Next]_<<count, victoryAnnounced, prisonerSignals, lampState, wardenRecord>>
    /\ WF_<<wardenAction>>_Prisoner

Init ==
    /\ count = 1
    /\ victoryAnnounced = FALSE
    /\ prisonerSignals = [p \in NonCounters |-> 0]
    /\ lampState = IF Light_Unknown THEN BOOLEAN ELSE FALSE
    /\ wardenRecord = {}

Next ==
    \/ wardenAction
    \/ (victoryAnnounced = FALSE) -> (\E p \in Prisoner : Signal(p))

Signal(p) ==
    LET nextSignals == [prisonerSignals EXCEPT ![p] = prisonerSignals[p] + 1]
        nextCount == IF p = Counter THEN count ELSE count
        nextVictoryAnnounced == victoryAnnounced
        nextLampState == lampState
        nextWardenRecord == wardenRecord
    IN
        \/ /\ p \in NonCounters
           /\ lampState = FALSE
           /\ nextSignals[p] < (IF Light_Unknown THEN 2 ELSE 1)
           /\ nextLampState' = TRUE
           /\ prisonerSignals' = nextSignals
           /\ count' = nextCount
           /\ victoryAnnounced' = nextVictoryAnnounced
           /\ lampState' = nextLampState
           /\ wardenRecord' = nextWardenRecord
        \/ /\ p = Counter
           /\ lampState = TRUE
           /\ nextCount' == IF Light_Unknown THEN count + 1 ELSE (count % N) + 1
           /\ nextVictoryAnnounced' == (IF Light_Unknown THEN nextCount' >= 2 * N - 1 ELSE nextCount' >= N)
           /\ nextLampState' = FALSE
           /\ prisonerSignals' = prisonerSignals
           /\ count' = nextCount'
           /\ victoryAnnounced' = nextVictoryAnnounced'
           /\ lampState' = nextLampState'
           /\ wardenRecord' = nextWardenRecord

wardenAction ==
    \E p \in Prisoner :
        LET nextWardenRecord == wardenRecord \cup {p}
        IN
            /\ prisonerSignals' = prisonerSignals
            /\ count' = count
            /\ victoryAnnounced' = victoryAnnounced
            /\ lampState' = lampState
            /\ wardenRecord' = nextWardenRecord

TYPEOK ==
    /\ count \in 1..(IF Light_Unknown THEN 2 * N - 1 ELSE N)
    /\ victoryAnnounced \in BOOLEAN
    /\ prisonerSignals \in [NonCounters -> 0..(IF Light_Unknown THEN 1 ELSE 0)]
    /\ lampState \in BOOLEAN
    /\ wardenRecord \in SUBSET Prisoner

VictoryOK ==
    \/ victoryAnnounced = FALSE
    \/ (victoryAnnounced = TRUE) /\ (wardenRecord = Prisoner)

Terminating ==
    <>[](victoryAnnounced)

====
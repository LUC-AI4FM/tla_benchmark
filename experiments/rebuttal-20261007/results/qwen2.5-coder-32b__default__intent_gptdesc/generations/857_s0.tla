------------------------------- MODULE PrisonersAndLightBulb -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MAX_SIGNAL_USES, INITIAL_LAMP_STATE_UNKNOWN

VARIABLES lampState, prisonerCount, prisonerSignals, announcementMade

Init == /\ lampState = IF INITIAL_LAMP_STATE_UNKNOWN THEN BOOLEAN ELSE FALSE
        /\ prisonerCount = 0
        /\ prisonerSignals = [p \in 1..N -> 0]
        /\ announcementMade = FALSE

Next ==
    \/ /\ \E p \in 1..N : 
            /\ prisonerSignals' = [prisonerSignals EXCEPT ![p] = (IF prisonerSignals[p] < MAX_SIGNAL_USES THEN prisonerSignals[p] + 1 ELSE prisonerSignals[p])]
            /\ lampState' = IF prisonerCount > 0 /\ lampState = FALSE THEN TRUE ELSE lampState
            /\ prisonerCount' = prisonerCount
            /\ announcementMade' = announcementMade
       \/ /\ \E p \in 1..N : 
            /\ prisonerSignals' = prisonerSignals
            /\ lampState' = IF lampState = TRUE THEN FALSE ELSE lampState
            /\ prisonerCount' = (IF lampState = TRUE AND prisonerSignals[p] = 0 THEN prisonerCount + 1 ELSE prisonerCount)
            /\ announcementMade' = announcementMade
       \/ /\ \E p \in 1..N : 
            /\ prisonerSignals' = prisonerSignals
            /\ lampState' = lampState
            /\ prisonerCount' = prisonerCount
            /\ announcementMade' = TRUE

Spec ==
    /\ Init
    /\ [][Next]_<<lampState, prisonerCount, prisonerSignals, announcementMade>>
    /\ WF_<<p \in 1..N >> (Next)

TypeInvariant ==
    /\ lampState \in BOOLEAN
    /\ prisonerCount \in 0..N
    /\ \A p \in 1..N : prisonerSignals[p] \in 0..MAX_SIGNAL_USES
    /\ announcementMade \in BOOLEAN

BoundednessInvariant ==
    /\ prisonerCount <= N
    /\ \A p \in 1..N : prisonerSignals[p] <= MAX_SIGNAL_USES

SafetyProperty ==
    \/ ~announcementMade
    \/ (announcementMade /\ prisonerCount = N)

LivenessProperty ==
    <>[](announcementMade /\ prisonerCount = N)

Invariants ==
    /\ TypeInvariant
    /\ BoundednessInvariant
    /\ SafetyProperty

THEOREM Spec => []Invariants

THEOREM Spec => LivenessProperty
=============================================================================
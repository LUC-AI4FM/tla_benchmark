---------------------------- MODULE PrisonerLightSwitch ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N  \* Number of prisoners

VARIABLES lightOn, counterVisited, otherPrisonersVisited, victoryAnnounced

Init == 
    /\ lightOn \in {FALSE, TRUE}
    /\ counterVisited = FALSE
    /\ otherPrisonersVisited = {}
    /\ victoryAnnounced = FALSE

Next ==
    \/ /\ lightOn
       /\ \/ /\ counterVisited
              /\ lightOn'
             /\ counterVisited' = TRUE
             /\ otherPrisonersVisited' = otherPrisonersVisited
             /\ victoryAnnounced' \in {FALSE, TRUE}
          \/ ~counterVisited
             /\ lightOn' = FALSE
             /\ counterVisited' = FALSE
             /\ otherPrisonersVisited' = (CHOOSE p \in (1..N) \ {counter} : TRUE)
             /\ victoryAnnounced' = FALSE
    \/ ~lightOn
       /\ \/ /\ counterVisited
              /\ lightOn'
             /\ counterVisited' = FALSE
             /\ otherPrisonersVisited' = (otherPrisonersVisited \union {CHOOSE p \in (1..N) \ {counter} : TRUE})
             /\ victoryAnnounced' = (IF CARDINALITY(otherPrisonersVisited) >= N - 1 THEN TRUE ELSE FALSE)
          \/ ~counterVisited
             /\ lightOn' = TRUE
             /\ counterVisited' = FALSE
             /\ otherPrisonersVisited' = (CHOOSE p \in (1..N) \ {counter} : TRUE)
             /\ victoryAnnounced' = FALSE

Spec ==
    INIT Init
    /\ SF_<<Next>>
    /\ WF_<<Next>>

SafetyInvariant ==
    \/ lightOn \in {FALSE, TRUE}
    /\ counterVisited \in BOOLEAN
    /\ otherPrisonersVisited \subseteq (1..N) \ {counter}
    /\ victoryAnnounced \in BOOLEAN

LivenessProperty ==
    <>(victoryAnnounced)

SpecWithInvariants ==
    Spec
    /\ []SafetyInvariant
    /\ LivenessProperty

================================================================================
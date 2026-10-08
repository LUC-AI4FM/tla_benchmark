------------------------------- MODULE TwoJugPuzzle -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    CAPACITY_3,
    CAPACITY_5

VARIABLES 
    jug3, 
    jug5, 
    generatedStates, 
    distinctStates, 
    diameter, 
    totalWaterDrawn

Init == /\ jug3 = 0
        /\ jug5 = 0
        /\ generatedStates = {<<0, 0>>}
        /\ distinctStates = {<<0, 0>>}
        /\ diameter = 0
        /\ totalWaterDrawn = 0

FillJug3 == 
    /\ jug3' = CAPACITY_3
    /\ jug5' = jug5
    /\ generatedStates' = generatedStates \cup {<<jug3', jug5'>>}
    /\ distinctStates' = distinctStates \cup {<<jug3', jug5'>>}
    /\ diameter' = Max(diameter, Cardinality(generatedStates) + 1)
    /\ totalWaterDrawn' = totalWaterDrawn + (CAPACITY_3 - jug3)

FillJug5 == 
    /\ jug3' = jug3
    /\ jug5' = CAPACITY_5
    /\ generatedStates' = generatedStates \cup {<<jug3', jug5'>>}
    /\ distinctStates' = distinctStates \cup {<<jug3', jug5'>>}
    /\ diameter' = Max(diameter, Cardinality(generatedStates) + 1)
    /\ totalWaterDrawn' = totalWaterDrawn + (CAPACITY_5 - jug5)

EmptyJug3 == 
    /\ jug3' = 0
    /\ jug5' = jug5
    /\ generatedStates' = generatedStates \cup {<<jug3', jug5'>>}
    /\ distinctStates' = distinctStates \cup {<<jug3', jug5'>>}
    /\ diameter' = Max(diameter, Cardinality(generatedStates) + 1)
    /\ totalWaterDrawn' = totalWaterDrawn

EmptyJug5 == 
    /\ jug3' = jug3
    /\ jug5' = 0
    /\ generatedStates' = generatedStates \cup {<<jug3', jug5'>>}
    /\ distinctStates' = distinctStates \cup {<<jug3', jug5'>>}
    /\ diameter' = Max(diameter, Cardinality(generatedStates) + 1)
    /\ totalWaterDrawn' = totalWaterDrawn

PourFrom3To5 ==
    /\ LET maxPour == Min(jug3, CAPACITY_5 - jug5) IN
       /\ jug3' = jug3 - maxPour
       /\ jug5' = jug5 + maxPour
       /\ generatedStates' = generatedStates \cup {<<jug3', jug5'>>}
       /\ distinctStates' = distinctStates \cup {<<jug3', jug5'>>}
       /\ diameter' = Max(diameter, Cardinality(generatedStates) + 1)
       /\ totalWaterDrawn' = totalWaterDrawn

PourFrom5To3 ==
    /\ LET maxPour == Min(jug5, CAPACITY_3 - jug3) IN
       /\ jug3' = jug3 + maxPour
       /\ jug5' = jug5 - maxPour
       /\ generatedStates' = generatedStates \cup {<<jug3', jug5'>>}
       /\ distinctStates' = distinctStates \cup {<<jug3', jug5'>>}
       /\ diameter' = Max(diameter, Cardinality(generatedStates) + 1)
       /\ totalWaterDrawn' = totalWaterDrawn

Next == \/ FillJug3
        \/ FillJug5
        \/ EmptyJug3
        \/ EmptyJug5
        \/ PourFrom3To5
        \/ PourFrom5To3

Spec == Init /\ [][Next]_<<jug3, jug5, generatedStates, distinctStates, diameter, totalWaterDrawn>>

SafetyInvariant == jug5 = 4

LivenessProperty == <>(jug5 = 4)

FairnessCondition == WF_next(Next)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => <>LivenessProperty
THEOREM Spec => FairnessCondition

=============================================================================
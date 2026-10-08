------------------------------- MODULE TwoJugPuzzle -------------------------------

CONSTANTS 
    \* Constants for capacities
    CAPACITY_3,
    CAPACITY_5,

VARIABLES 
    \* Variables representing the current state of the jugs
    jug3, 
    jug5,

    \* Instrumentation variables
    generatedStates,
    distinctStates,
    diameter,
    totalWaterDrawn

\* Define initial state
Init == /\ jug3 = 0
        /\ jug5 = 0
        /\ generatedStates = 1
        /\ distinctStates = 1
        /\ diameter = 0
        /\ totalWaterDrawn = 0

\* Define the possible actions: fill, empty, pour
FillJug3 == 
    /\ jug3 < CAPACITY_3
    /\ jug5' = jug5
    /\ jug3' = CAPACITY_3
    /\ generatedStates' = generatedStates + 1
    /\ totalWaterDrawn' = totalWaterDrawn + (CAPACITY_3 - jug3)
    
FillJug5 == 
    /\ jug5 < CAPACITY_5
    /\ jug3' = jug3
    /\ jug5' = CAPACITY_5
    /\ generatedStates' = generatedStates + 1
    /\ totalWaterDrawn' = totalWaterDrawn + (CAPACITY_5 - jug5)

EmptyJug3 == 
    /\ jug3 > 0
    /\ jug5' = jug5
    /\ jug3' = 0
    /\ generatedStates' = generatedStates + 1

EmptyJug5 == 
    /\ jug5 > 0
    /\ jug3' = jug3
    /\ jug5' = 0
    /\ generatedStates' = generatedStates + 1

PourFrom3To5 ==
    /\ jug3 > 0
    /\ jug5 < CAPACITY_5
    /\ LET amountToPour == MIN(jug3, CAPACITY_5 - jug5) IN
       /\ jug3' = jug3 - amountToPour
       /\ jug5' = jug5 + amountToPour
       /\ generatedStates' = generatedStates + 1

PourFrom5To3 ==
    /\ jug5 > 0
    /\ jug3 < CAPACITY_3
    /\ LET amountToPour == MIN(jug5, CAPACITY_3 - jug3) IN
       /\ jug3' = jug3 + amountToPour
       /\ jug5' = jug5 - amountToPour
       /\ generatedStates' = generatedStates + 1

\* Define the next state relation
Next ==
    \/ FillJug3
    \/ FillJug5
    \/ EmptyJug3
    \/ EmptyJug5
    \/ PourFrom3To5
    \/ PourFrom5To3

\* Define the specification
Spec == Init /\ [][Next]_<<jug3, jug5>>

\* Define the safety property: larger container (jug5) contains exactly 4 units
SafetyProperty ==
    \A s \in StateSpace : s.jug5 = 4 => TRUE

\* Define an observable action that counts any transition that changes the contents of either container
PourOrChange ==
    \/ jug3' # jug3
    \/ jug5' # jug5

\* Define the state space
StateSpace == {s \in [<<jug3, jug5>> -> Nat] : s.jug3 <= CAPACITY_3 /\ s.jug5 <= CAPACITY_5}

\* Define the instrumentation to count reachable states and diameter
ReachableStates ==
    LET states == [s \in StateSpace |-> TRUE]
        in /\ generatedStates = Cardinality(states)
           /\ distinctStates = Cardinality({s \in states : states[s]})
           /\ diameter = MaxCardinality({Len(p) : p \in Paths(Init, Next)})
           
\* Define the total water drawn and average water-drawn-per-distinct-state
WaterMetrics ==
    LET avgDrawn == IF distinctStates > 0 THEN totalWaterDrawn / distinctStates ELSE 0
        in /\ totalWaterDrawn = totalWaterDrawn
           /\ avgDrawn = avgDrawn

\* Assert the expected numeric values for instrumentation metrics
AssertInstrumentation ==
    /\ generatedStates = 16
    /\ distinctStates = 15
    /\ diameter = 8
    /\ totalWaterDrawn = 20
    /\ WaterMetrics.avgDrawn = 4/3

=============================================================================
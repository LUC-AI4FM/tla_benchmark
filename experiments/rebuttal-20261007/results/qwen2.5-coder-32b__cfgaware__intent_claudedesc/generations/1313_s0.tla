------------------------------- MODULE DieHard -------------------------------

CONSTANTS
    \* Constants for jug capacities
    JUG3_CAPACITY,
    JUG5_CAPACITY

VARIABLES
    \* Variables representing the current amount of water in each jug
    jug3,
    jug5,
    \* Variable to track total gallons drawn from the fountain
    totalDrawn

\* Type invariants for jugs and totalDrawn
INVARIANT_TYPE == /\ jug3 \in 0..JUG3_CAPACITY
                 /\ jug5 \in 0..JUG5_CAPACITY
                 /\ totalDrawn \geq 0

\* Initial state: both jugs are empty, no water has been drawn from the fountain
Init == /\ jug3 = 0
        /\ jug5 = 0
        /\ totalDrawn = 0

\* Action to fill the 3-gallon jug to capacity
FillJug3 == /\ jug3' = JUG3_CAPACITY
            /\ jug5' = jug5
            /\ totalDrawn' = totalDrawn + (JUG3_CAPACITY - jug3)

\* Action to fill the 5-gallon jug to capacity
FillJug5 == /\ jug3' = jug3
            /\ jug5' = JUG5_CAPACITY
            /\ totalDrawn' = totalDrawn + (JUG5_CAPACITY - jug5)

\* Action to empty the 3-gallon jug completely
EmptyJug3 == /\ jug3' = 0
             /\ jug5' = jug5
             /\ totalDrawn' = totalDrawn

\* Action to empty the 5-gallon jug completely
EmptyJug5 == /\ jug3' = jug3
             /\ jug5' = 0
             /\ totalDrawn' = totalDrawn

\* Action to pour water from the 3-gallon jug into the 5-gallon jug
PourFromJug3ToJug5 ==
    LET amountToPour == MIN(jug3, JUG5_CAPACITY - jug5) IN
        /\ jug3' = jug3 - amountToPour
        /\ jug5' = jug5 + amountToPour
        /\ totalDrawn' = totalDrawn

\* Action to pour water from the 5-gallon jug into the 3-gallon jug
PourFromJug5ToJug3 ==
    LET amountToPour == MIN(jug5, JUG3_CAPACITY - jug3) IN
        /\ jug3' = jug3 + amountToPour
        /\ jug5' = jug5 - amountToPour
        /\ totalDrawn' = totalDrawn

\* Next state relation: any of the above actions can be taken
Next == \/ FillJug3
        \/ FillJug5
        \/ EmptyJug3
        \/ EmptyJug5
        \/ PourFromJug3ToJug5
        \/ PourFromJug5ToJug3

\* Specification: initial state and next-state relation, with type invariants
Spec == /\ Init
        /\ [][Next]_<<jug3, jug5, totalDrawn>>
        /\ INVARIANT_TYPE

\* Property to check if the big jug (5-gallon) contains exactly 4 gallons
PROPERTY_Jug5HasFourGallons == jug5 = 4

\* Property to count states where both jugs change simultaneously
PROPERTY_BothJugsChange ==
    \/ (jug3 # jug3' /\ jug5 # jug5')
    \/ (jug3 # jug3' /\ jug5 # jug5')

=============================================================================
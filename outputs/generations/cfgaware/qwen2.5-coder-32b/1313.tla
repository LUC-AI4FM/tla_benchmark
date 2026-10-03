------------------------------- MODULE DieHard -------------------------------

CONSTANTS
    \* Constants for jug capacities
    SMALL_JUG_CAPACITY,
    BIG_JUG_CAPACITY

VARIABLES
    \* Variables representing the current amount of water in each jug
    smallJug,
    bigJug,
    \* Custom counter to track total water usage
    waterUsageCounter

\* Initial state: both jugs are empty and no water has been used yet
Init == /\ smallJug = 0
        /\ bigJug = 0
        /\ waterUsageCounter = 0

\* Action to fill the small jug to its capacity
FillSmall == /\ smallJug' = SMALL_JUG_CAPACITY
               /\ bigJug' = bigJug
               /\ waterUsageCounter' = waterUsageCounter + SMALL_JUG_CAPACITY

\* Action to fill the big jug to its capacity
FillBig == /\ smallJug' = smallJug
            /\ bigJug' = BIG_JUG_CAPACITY
            /\ waterUsageCounter' = waterUsageCounter + BIG_JUG_CAPACITY

\* Action to empty the small jug
EmptySmall == /\ smallJug' = 0
                /\ bigJug' = bigJug
                /\ waterUsageCounter' = waterUsageCounter

\* Action to empty the big jug
EmptyBig == /\ smallJug' = smallJug
              /\ bigJug' = 0
              /\ waterUsageCounter' = waterUsageCounter

\* Action to pour from the small jug into the big jug until either the small jug is empty or the big jug is full
PourSmallToBig == LET amountToPour \in (MIN(smallJug, BIG_JUG_CAPACITY - bigJug)) IN
                    /\ smallJug' = smallJug - amountToPour
                    /\ bigJug' = bigJug + amountToPour
                    /\ waterUsageCounter' = waterUsageCounter

\* Action to pour from the big jug into the small jug until either the big jug is empty or the small jug is full
PourBigToSmall == LET amountToPour \in (MIN(bigJug, SMALL_JUG_CAPACITY - smallJug)) IN
                    /\ smallJug' = smallJug + amountToPour
                    /\ bigJug' = bigJug - amountToPour
                    /\ waterUsageCounter' = waterUsageCounter

\* Next-state relation: any of the above actions can be taken
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ PourSmallToBig
        \/ PourBigToSmall

\* Temporal specification: initial state and stuttering-closed next-state relation
Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsageCounter>>

\* Predicate to check if the big jug has 4 gallons of water
BigJugHasFourGallons == (bigJug = 4)

\* TLC-specific operator to track and inspect model-checking statistics
CONSTANTS _tc

\* Predicate to check that the state space contains a state where the big jug has 4 gallons
CheckBigJugHasFourGallons ==
    \E s \in _tc : (s.bigJug = 4)

\* Predicate to check certain action/state-count expectations after model checking
CONSTANTS EXPECTED_ACTION_COUNT, EXPECTED_STATE_COUNT

CheckActionAndStateCounts ==
    /\ Len(_tc) = EXPECTED_STATE_COUNT
    /\ TLCGet("NumberOfStatesGenerated") = EXPECTED_STATE_COUNT
    /\ TLCGet("NumberOfDistinctStates") \leq EXPECTED_STATE_COUNT
    /\ TLCGet("NumberOfActionsGenerated") = EXPECTED_ACTION_COUNT

=============================================================================
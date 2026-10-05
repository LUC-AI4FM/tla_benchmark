---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers, TLC

VARIABLES big, small

\* Constants for jug capacities
BigCapacity == 5
SmallCapacity == 3

\* Type invariant: both jugs within their capacity bounds
TypeOK == /\ big \in 0..BigCapacity
          /\ small \in 0..SmallCapacity

\* Initial state: both jugs empty
Init == /\ big = 0
        /\ small = 0

\* Fill the small jug to capacity
FillSmall == /\ small' = SmallCapacity
             /\ big' = big
             /\ TLCSet(42, TLCGet(42) + SmallCapacity)

\* Fill the big jug to capacity
FillBig == /\ big' = BigCapacity
           /\ small' = small
           /\ TLCSet(42, TLCGet(42) + BigCapacity)

\* Empty the small jug completely
EmptySmall == /\ small' = 0
              /\ big' = big

\* Empty the big jug completely
EmptyBig == /\ big' = 0
            /\ small' = small

\* Pour from small to big (stops when source empty or destination full)
SmallToBig == LET amount == IF small + big <= BigCapacity
                            THEN small
                            ELSE BigCapacity - big
              IN /\ small' = small - amount
                 /\ big' = big + amount

\* Pour from big to small (stops when source empty or destination full)
BigToSmall == LET amount == IF big + small <= SmallCapacity
                            THEN big
                            ELSE SmallCapacity - small
              IN /\ big' = big - amount
                 /\ small' = small + amount

\* Next state relation: any of the six actions
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

\* Temporal specification with stuttering
Spec == Init /\ [][Next]_<<big, small>>

\* Goal state: big jug contains exactly 4 gallons
HasFour == big = 4

\* Pour action: both jugs change simultaneously
PourAction == big' # big /\ small' # small

\* Annotation for tracking reachability of HasFour
HasFour_POSSIBLE == HasFour

\* Annotation for tracking reachability of PourAction (in next states)
PourAction_POSSIBLE == ENABLED (SmallToBig \/ BigToSmall)

\* Expected counts for possibility tracking
PossibleCounts == /\ TLCGet("spec")["hasfourfour_possible"] = 8
                  /\ TLCGet("spec")["pouraction_possible"] = 14

\* Post-condition for model checking statistics
PostCondition == /\ TLCGet("generated") = 97
                 /\ TLCGet("distinct") = 16
                 /\ TLCGet("diameter") = 8
                 /\ TLCGet(42) = 128

==========================================================================
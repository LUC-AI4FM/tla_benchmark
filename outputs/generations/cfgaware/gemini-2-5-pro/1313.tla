---- MODULE DieHard ----
EXTENDS Integers, TLC

CONSTANTS SmallCapacity, BigCapacity

ASSUME  /\ SmallCapacity = 3
        /\ BigCapacity = 5

VARIABLES small, big, water_used

vars == <<small, big, water_used>>

\* The initial state: both jugs are empty and no water has been used.
Init == /\ small = 0
        /\ big = 0
        /\ water_used = 0

\* Fill the small jug to its capacity.
FillSmall ==
    /\ small < SmallCapacity
    /\ small' = SmallCapacity
    /\ big' = big
    /\ water_used' = water_used + (SmallCapacity - small)

\* Fill the big jug to its capacity.
FillBig ==
    /\ big < BigCapacity
    /\ big' = BigCapacity
    /\ small' = small
    /\ water_used' = water_used + (BigCapacity - big)

\* Empty the small jug.
EmptySmall ==
    /\ small > 0
    /\ small' = 0
    /\ big' = big
    /\ UNCHANGED water_used

\* Empty the big jug.
EmptyBig ==
    /\ big > 0
    /\ big' = 0
    /\ small' = small
    /\ UNCHANGED water_used

\* Pour from the small jug to the big jug until the small one is empty
\* or the big one is full.
PourSmallToBig ==
    /\ small > 0
    /\ big < BigCapacity
    /\ LET total == small + big
       IN /\ big' = IF total > BigCapacity THEN BigCapacity ELSE total
          /\ small' = total - big'
          /\ UNCHANGED water_used

\* Pour from the big jug to the small jug until the big one is empty
\* or the small one is full.
PourBigToSmall ==
    /\ big > 0
    /\ small < SmallCapacity
    /\ LET total == small + big
       IN /\ small' = IF total > SmallCapacity THEN SmallCapacity ELSE total
          /\ big' = total - small'
          /\ UNCHANGED water_used

\* The next-state relation is the disjunction of all possible actions.
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ PourSmallToBig
        \/ PourBigToSmall

\* The main temporal specification.
Spec == Init /\ [][Next]_vars

\* A property stating that a state where the big jug contains 4 gallons is reachable.
\* This is intended to be checked as a temporal property by TLC.
TargetStateFound == <>(big = 4)

\* A predicate that uses TLC-specific operators to check model-checking statistics.
\* This is intended to be checked as a model constraint by TLC.
\* The value is based on a breadth-first search run of this model.
TLCStatistics == TLCGet("distinctStates") = 16

=============================================================================
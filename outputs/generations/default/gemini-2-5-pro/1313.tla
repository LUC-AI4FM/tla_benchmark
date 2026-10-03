---- MODULE DieHard ----
EXTENDS Integers, TLC

CONSTANTS
    SmallJugCapacity,
    BigJugCapacity

\* This specification models the classic problem with 3 and 5 gallon jugs.
SmallJugCapacity == 3
BigJugCapacity == 5

VARIABLES
    small,      \* Current amount of water in the small jug
    big,        \* Current amount of water in the big jug
    waterUsed   \* Cumulative counter of water taken from the tap

vars == <<small, big, waterUsed>>

\* The type invariant, specifying the valid range for each state variable.
TypeOK ==
    /\ small \in 0..SmallJugCapacity
    /\ big \in 0..BigJugCapacity
    /\ waterUsed \in Nat

\* The initial state: both jugs are empty.
Init ==
    /\ small = 0
    /\ big = 0
    /\ waterUsed = 0

\* Action: Fill the small jug to its capacity from the tap.
FillSmall ==
    /\ small < SmallJugCapacity
    /\ small' = SmallJugCapacity
    /\ big' = big
    /\ waterUsed' = waterUsed + (SmallJugCapacity - small)

\* Action: Fill the big jug to its capacity from the tap.
FillBig ==
    /\ big < BigJugCapacity
    /\ small' = small
    /\ big' = BigJugCapacity
    /\ waterUsed' = waterUsed + (BigJugCapacity - big)

\* Action: Empty the small jug.
EmptySmall ==
    /\ small > 0
    /\ small' = 0
    /\ big' = big
    /\ UNCHANGED waterUsed

\* Action: Empty the big jug.
EmptyBig ==
    /\ big > 0
    /\ small' = small
    /\ big' = 0
    /\ UNCHANGED waterUsed

\* Action: Pour from the small jug into the big one until the small one is
\* empty or the big one is full.
PourSmallToBig ==
    /\ small > 0
    /\ big < BigJugCapacity
    LET amount == Min(small, BigJugCapacity - big) IN
    /\ small' = small - amount
    /\ big' = big + amount
    /\ UNCHANGED waterUsed

\* Action: Pour from the big jug into the small one until the big one is
\* empty or the small one is full.
PourBigToSmall ==
    /\ big > 0
    /\ small < SmallJugCapacity
    LET amount == Min(big, SmallJugCapacity - small) IN
    /\ big' = big - amount
    /\ small' = small + amount
    /\ UNCHANGED waterUsed

\* The next-state relation is the disjunction of all possible actions.
Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ PourSmallToBig
    \/ PourBigToSmall

\* The complete specification, stating that the system starts in Init and
\* forever takes steps defined by Next (or stutters).
Spec == Init /\ [][Next]_vars

\* =============================================================================
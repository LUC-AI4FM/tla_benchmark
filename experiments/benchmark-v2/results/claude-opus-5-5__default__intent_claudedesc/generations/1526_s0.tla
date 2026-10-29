------------------------------ MODULE SingleLaneBridge ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsLeft,    \* cars travelling from left to right (increasing positions)
          CarsRight,   \* cars travelling from right to left (decreasing positions)
          Bridge,      \* set of positions forming the single-lane bridge
          N            \* number of positions on the (circular) roadway

Positions == 1..N
Cars      == CarsLeft \cup CarsRight

MinB == CHOOSE m \in Bridge : \A b \in Bridge : m <= b
MaxB == CHOOSE m \in Bridge : \A b \in Bridge : m >= b

ASSUME /\ N \in Nat
       /\ CarsLeft \cap CarsRight = {}
       /\ Cars # {}
       /\ Bridge # {}
       /\ Bridge \subseteq Positions
       /\ Bridge = MinB..MaxB          \* bridge is contiguous
       /\ MinB > 1                     \* there is an approach area on the left
       /\ MaxB < N                     \* there is an approach area on the right

VARIABLES location,   \* location[c] : current position of car c
          waiting     \* FIFO queue of cars waiting at the bridge entrance

vars == <<location, waiting>>

-----------------------------------------------------------------------------
\* Helper definitions

SameDir(c, d) == (c \in CarsLeft /\ d \in CarsLeft) \/ (c \in CarsRight /\ d \in CarsRight)

\* Next position along the car's direction of travel (roadway wraps around,
\* so cars repeatedly approach the bridge)
NextPos(c) ==
    IF c \in CarsLeft
        THEN IF location[c] = N THEN 1 ELSE location[c] + 1
        ELSE IF location[c] = 1 THEN N ELSE location[c] - 1

\* Position directly in front of the bridge where a car must wait
WaitPos(c) == IF c \in CarsLeft THEN MinB - 1 ELSE MaxB + 1

\* Next position is not occupied by another car in the same lane/direction
NextFree(c) == \A d \in Cars \ {c} : SameDir(c, d) => location[d] # NextPos(c)

OnBridge(c) == location[c] \in Bridge

\* No car from the opposite direction is on the bridge
NoOppositeOnBridge(c) == \A d \in Cars : (~SameDir(c, d) /\ OnBridge(d)) => FALSE

InQueue(c) == \E i \in 1..Len(waiting) : waiting[i] = c

-----------------------------------------------------------------------------
TypeOK ==
    /\ location \in [Cars -> Positions]
    /\ waiting \in Seq(Cars)

Init ==
    /\ location \in { f \in [Cars -> Positions] :
                        /\ \A c \in Cars : f[c] \notin Bridge
                        /\ \A c \in Cars : f[c] # WaitPos(c)
                        /\ \A c, d \in Cars : (c # d /\ SameDir(c, d)) => f[c] # f[d] }
    /\ waiting = <<>>

\* A car moves one step forward along its lane (not entering the bridge).
\* If it reaches the bridge entrance it joins the waiting queue.
Move(c) ==
    /\ location[c] # WaitPos(c)
    /\ NextFree(c)
    /\ location' = [location EXCEPT ![c] = NextPos(c)]
    /\ waiting' = IF NextPos(c) = WaitPos(c) THEN Append(waiting, c) ELSE waiting

\* The car at the head of the waiting queue enters the bridge, provided that
\* no car from the opposite direction is on the bridge.
Enter(c) ==
    /\ waiting # <<>>
    /\ Head(waiting) = c
    /\ location[c] = WaitPos(c)
    /\ NoOppositeOnBridge(c)
    /\ NextFree(c)
    /\ location' = [location EXCEPT ![c] = NextPos(c)]
    /\ waiting' = Tail(waiting)

Next == \E c \in Cars : Move(c) \/ Enter(c)

Fairness == \A c \in Cars : WF_vars(Move(c)) /\ WF_vars(Enter(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* No head-on collisions: cars of opposite directions never on the bridge together
NoHeadOnCollision ==
    ~(\E l \in CarsLeft, r \in CarsRight : OnBridge(l) /\ OnBridge(r))

\* No physical overlap: two distinct cars in the same lane never share a position,
\* and no two distinct cars ever share a bridge position
NoOverlap ==
    /\ \A c, d \in Cars : (c # d /\ SameDir(c, d)) => location[c] # location[d]
    /\ \A c, d \in Cars : (c # d /\ OnBridge(c) /\ OnBridge(d)) => location[c] # location[d]

\* Waiting queue is consistent with the cars' positions
QueueConsistent ==
    /\ \A c \in Cars : InQueue(c) <=> location[c] = WaitPos(c)
    /\ \A i, j \in 1..Len(waiting) : i # j => waiting[i] # waiting[j]

Safety == TypeOK /\ NoHeadOnCollision /\ NoOverlap /\ QueueConsistent

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
\* Liveness properties

\* Progress / no starvation: every waiting car eventually gets onto the bridge
WaitingLeadsToBridge ==
    \A c \in Cars : (location[c] = WaitPos(c)) ~> OnBridge(c)

\* Fair access: every car (from both directions) is on the bridge infinitely often
FairAccess ==
    \A c \in Cars : []<>OnBridge(c)

\* Both directions repeatedly get to use the bridge
BothDirectionsServed ==
    /\ []<>(\E l \in CarsLeft  : OnBridge(l))
    /\ []<>(\E r \in CarsRight : OnBridge(r))

THEOREM Spec => (WaitingLeadsToBridge /\ FairAccess /\ BothDirectionsServed)

=============================================================================
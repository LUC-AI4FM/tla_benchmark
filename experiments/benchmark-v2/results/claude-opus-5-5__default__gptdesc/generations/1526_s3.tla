------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Model-checking configuration for a single-lane bridge system.           *)
(* Cars on the right drive leftwards and cars on the left drive rightwards *)
(* along a circular road of Positions. The road has a single-lane Bridge   *)
(* that cars may only cross in one direction at a time. Cars arriving at   *)
(* the bridge wait in a FIFO queue, which guarantees that no car starves.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

\* Constant definitions (substituted for the CONSTANTS in the TLC config)
const_CarsRight == {"r1", "r2"}
const_CarsLeft  == {"l1", "l2"}
const_Bridge    == {4, 5, 6}
const_Positions == {1, 2, 3, 4, 5, 6, 7, 8, 9}

-----------------------------------------------------------------------------
Cars == CarsRight \cup CarsLeft

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

ASSUME /\ CarsRight \cap CarsLeft = {}
       /\ Positions \subseteq Nat
       /\ Bridge \subseteq Positions
       /\ Bridge # {}
       /\ Min(Bridge) - 1 \in Positions
       /\ Max(Bridge) + 1 \in Positions

Range(s) == {s[i] : i \in DOMAIN s}

\* Right cars drive towards smaller positions, left cars towards larger ones;
\* the road wraps around so that cars keep returning to the bridge.
NextPos(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = Min(Positions) THEN Max(Positions) ELSE Location[c] - 1
    ELSE IF Location[c] = Max(Positions) THEN Min(Positions) ELSE Location[c] + 1

\* The position just before the bridge, where a car must wait.
EntryPoint(c) == IF c \in CarsRight THEN Max(Bridge) + 1 ELSE Min(Bridge) - 1

\* The first bridge position a car occupies after entering.
StartBridge(c) == IF c \in CarsRight THEN Max(Bridge) ELSE Min(Bridge)

Opposite(c) == IF c \in CarsRight THEN CarsLeft ELSE CarsRight

Occupied(p) == \E d \in Cars : Location[d] = p

-----------------------------------------------------------------------------
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsRight THEN Max(Positions)
                                                     ELSE Min(Positions)]
    /\ WaitingBeforeBridge = <<>>

\* Ordinary movement (anywhere except entering the bridge).
\* A bridge position can hold at most one car.
Move(c) ==
    /\ Location[c] # EntryPoint(c)
    /\ LET p == NextPos(c) IN
         /\ p \in Bridge => ~Occupied(p)
         /\ Location' = [Location EXCEPT ![c] = p]
    /\ UNCHANGED WaitingBeforeBridge

\* A car arriving at the bridge joins the waiting queue.
Wait(c) ==
    /\ Location[c] = EntryPoint(c)
    /\ c \notin Range(WaitingBeforeBridge)
    /\ WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
    /\ UNCHANGED Location

\* The car at the head of the queue enters the bridge once no car of the
\* opposite direction is on it and the first bridge position is free.
Enter(c) ==
    /\ Location[c] = EntryPoint(c)
    /\ WaitingBeforeBridge # <<>>
    /\ Head(WaitingBeforeBridge) = c
    /\ \A d \in Opposite(c) : Location[d] \notin Bridge
    /\ ~Occupied(StartBridge(c))
    /\ Location' = [Location EXCEPT ![c] = StartBridge(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next == \E c \in Cars : Move(c) \/ Wait(c) \/ Enter(c)

Fairness ==
    \A c \in Cars : /\ WF_vars(Move(c))
                    /\ WF_vars(Wait(c))
                    /\ WF_vars(Enter(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

\* Cars never travel the bridge in opposite directions simultaneously.
NoOppositeOnBridge ==
    ~(\E r \in CarsRight, l \in CarsLeft :
          Location[r] \in Bridge /\ Location[l] \in Bridge)

\* No two cars share a bridge position.
NoCollisionOnBridge ==
    \A c, d \in Cars :
        (c # d /\ Location[c] \in Bridge) => Location[c] # Location[d]

\* The waiting queue contains each car at most once.
QueueNoDuplicates ==
    \A i, j \in DOMAIN WaitingBeforeBridge :
        WaitingBeforeBridge[i] = WaitingBeforeBridge[j] => i = j

Safety == TypeOK /\ NoOppositeOnBridge /\ NoCollisionOnBridge /\ QueueNoDuplicates

(* Liveness *)

\* Every car on the right is infinitely often on the bridge.
CarsInfOftenOnBridge ==
    \A car \in CarsRight : []<>(Location[car] \in Bridge)

\* Every car on the left is also infinitely often on the bridge.
CarsLeftInfOftenOnBridge ==
    \A car \in CarsLeft : []<>(Location[car] \in Bridge)

THEOREM Spec => []Safety
THEOREM Spec => CarsInfOftenOnBridge
=============================================================================
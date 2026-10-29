---------------------------- MODULE CoffeeCan -------------------------------
(***************************************************************************)
(* The Coffee Can problem (Dijkstra & Scholten, popularized by Gries).     *)
(* A can holds black and white beans. Each step removes beans per the     *)
(* rules below, until exactly one bean remains.                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

Init ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* Two black beans picked: both removed, one black bean put back.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans picked: both removed, one black bean added.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One of each picked: black discarded, white returned.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean remains: stutter.
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_can /\ WF_can(Next)

-----------------------------------------------------------------------------

MonotonicDecrease == [][BeanCount' < BeanCount]_can

EventuallyTerminates == <>(ENABLED Termination)

LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_can

TerminationHypothesis ==
    /\ (can.white % 2 = 0) => <>(can.black = 1 /\ can.white = 0)
    /\ (can.white % 2 = 1) => <>(can.black = 0 /\ can.white = 1)

=============================================================================
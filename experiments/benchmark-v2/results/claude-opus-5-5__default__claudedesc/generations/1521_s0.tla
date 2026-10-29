------------------------------ MODULE CoffeeCan -----------------------------
(***************************************************************************)
(* The Coffee Can problem (Dijkstra & Scholten, popularized by Gries).     *)
(* A can holds black and white beans. Repeatedly pick two beans:           *)
(*  - two black: remove both, put one black back (net -1 black)            *)
(*  - two white: remove both, put one black in (net -2 white, +1 black)    *)
(*  - one of each: discard the black, return the white (net -1 black)      *)
(* The process ends when a single bean remains.                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

Init ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

\* Pick two black beans; put one black bean back.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Pick two white beans; discard both and add one black bean.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Pick one of each color; discard the black and return the white.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Stuttering step once exactly one bean remains.
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
(* Properties *)

\* Every non-stuttering step strictly decreases the number of beans.
MonotonicDecrease == [][BeanCount' < BeanCount]_can

\* The parity of the number of white beans is preserved by every step.
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_can

\* The process eventually reaches a single bean whose color is determined
\* by the parity of the initial number of white beans.
TerminationHypothesis ==
    IF can.white % 2 = 0
        THEN <>(can.black = 1 /\ can.white = 0)
        ELSE <>(can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis
=============================================================================
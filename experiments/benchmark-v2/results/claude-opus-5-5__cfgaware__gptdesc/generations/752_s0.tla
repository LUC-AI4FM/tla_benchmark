---------------------------- MODULE ApaCoffeeCan ----------------------------
(***************************************************************************)
(* Wrapper around the CoffeeCan specification that adds Apalache-oriented  *)
(* type annotations. The CoffeeCan definitions are given inline here so    *)
(* that this module parses on its own, without a separate CoffeeCan file.  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE
    \* @type: [black: Int, white: Int];
    can

-----------------------------------------------------------------------------
(* CoffeeCan definitions *)

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant == can \in Can

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Draw two black beans: throw both out, put one black bean back.
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Draw two white beans: throw both out, put one black bean back.
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Draw one bean of each colour: throw the black one out, put the white one back.
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_can /\ WF_can(Next)

EventuallyTerminates == <>(ENABLED Termination)

MonotonicDecrease == [][BeanCount' < BeanCount \/ BeanCount = 1]_can

LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_can

=============================================================================
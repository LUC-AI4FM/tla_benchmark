---------------------------- MODULE ApaCoffeeCan ----------------------------
(***************************************************************************)
(* Wrapper adding Apalache type annotations to the CoffeeCan spec. The     *)
(* CoffeeCan definitions are inlined so the module is self-contained.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE
    \* @type: { black : Int, white : Int };
    can

\* Set of all possible can states
Can == [black : Nat, white : Nat]

\* The can is a record of non-negative bean counts
TypeInvariant == can \in Can

\* Initially the can holds between 1 and MaxBeanCount beans
Init ==
    can \in {c \in [black : 0..MaxBeanCount, white : 0..MaxBeanCount] :
                c.black + c.white \in 1..MaxBeanCount}

BeanCount == can.black + can.white

\* Two black beans picked: discard both, put one black bean back
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans picked: discard both, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One of each picked: discard black, put white back
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Only one bean left: stutter
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_can

\* The number of beans strictly decreases until one bean remains
MonotonicDecrease == [][BeanCount > 1 => BeanCount' < BeanCount]_can

\* Eventually only one bean remains
EventuallyTerminates == <>(ENABLED Termination)

\* The parity of white beans is preserved; it determines the final color
LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_can

TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)
=============================================================================
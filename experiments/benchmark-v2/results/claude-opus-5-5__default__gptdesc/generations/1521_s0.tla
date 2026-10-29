---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCountAssumption ==
    /\ MaxBeanCount \in Nat
    /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

-----------------------------------------------------------------------------
(* Initial state: some positive, bounded number of beans in the can.       *)

Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

-----------------------------------------------------------------------------
(* Actions                                                                  *)

(* Two black beans removed: discard both, put one black bean back. *)
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Two white beans removed: discard both, put one black bean in. *)
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

(* One black and one white removed: discard black, put white back. *)
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Exactly one bean remains: stutter forever. *)
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorBlack
    \/ PickSameColorWhite
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                               *)

TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

(* The total number of beans strictly decreases on every non-stuttering step. *)
MonotonicDecrease ==
    [][BeanCount' < BeanCount]_vars

(* Eventually exactly one bean remains. *)
EventuallyTerminates ==
    <>(ENABLED Termination)

(* The parity of the number of white beans never changes. *)
LoopInvariant ==
    [][can'.white % 2 = can.white % 2]_vars

(* If the initial white count is even, the final bean is black;            *)
(* otherwise the final bean is white.                                      *)
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventuallyTerminates
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis

=============================================================================
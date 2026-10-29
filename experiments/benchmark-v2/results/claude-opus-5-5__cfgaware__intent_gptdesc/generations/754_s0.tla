---------------------------- MODULE CoffeeCan ----------------------------
(***************************************************************************)
(* The classical "coffee can" problem.  A can contains some white and     *)
(* black beans.  Repeatedly pick two beans:                                *)
(*   - same color      : remove both, put one black bean back;             *)
(*   - different color : remove both, put the white bean back.             *)
(* The process stops when a single bean remains.  The parity of the        *)
(* number of white beans is invariant, which determines the final color.   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCountAssumption == MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

TypeInvariant ==
    /\ can \in Can
    /\ can.black \in Nat
    /\ can.white \in Nat
    /\ BeanCount \in 1..MaxBeanCount

Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

(* Two white beans: remove both, add one black bean. *)
PickSameColorWhite ==
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.white = @ - 2, !.black = @ + 1]

(* Two black beans: remove both, add one black bean. *)
PickSameColorBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

(* One of each: remove both, return the white bean. *)
PickDifferentColor ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Terminal state: exactly one bean remains. *)
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

(* Every real update decreases the total count by exactly one. *)
MonotonicDecrease == [][BeanCount' = BeanCount - 1]_vars

(* The process eventually reaches a state with exactly one bean. *)
EventuallyTerminates == <>(ENABLED Termination)

(* The parity of the white count is preserved by every transition. *)
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

(* The final bean's color is determined by the initial parity of whites. *)
TerminationHypothesis ==
    IF can.white % 2 = 0
        THEN <>(can.black = 1 /\ can.white = 0)
        ELSE <>(can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => LoopInvariant
THEOREM Spec => EventuallyTerminates
THEOREM Spec => TerminationHypothesis
=============================================================================
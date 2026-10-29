------------------------------ MODULE CoffeeCan ------------------------------
(***************************************************************************)
(* The Coffee Can Bean Problem.                                            *)
(*                                                                         *)
(* A coffee can initially contains some number of black and white beans.  *)
(* One repeatedly removes two beans from the can and applies these rules:  *)
(*   - Both black: discard both, put one black bean back in.               *)
(*   - Both white: discard both, put one black bean back in.               *)
(*   - One of each: discard the black one, put the white one back in.      *)
(* Each step reduces the total number of beans by exactly one. The         *)
(* process stops when exactly one bean remains.                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCountAssumption ==
    /\ MaxBeanCount \in Nat
    /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

(***************************************************************************)
(* The set of all possible can contents.                                  *)
(***************************************************************************)
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeInvariant ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

(***************************************************************************)
(* Initial state: any can with between 1 and MaxBeanCount beans.          *)
(***************************************************************************)
Init ==
    can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

(***************************************************************************)
(* Remove two black beans; put one black bean back.                       *)
(***************************************************************************)
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

(***************************************************************************)
(* Remove two white beans; put one black bean in.                         *)
(***************************************************************************)
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

(***************************************************************************)
(* Remove one black and one white bean; put the white bean back.          *)
(***************************************************************************)
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

(***************************************************************************)
(* Termination: exactly one bean remains; the system stutters.            *)
(***************************************************************************)
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
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* Every non-stuttering step strictly decreases the total bean count. *)
MonotonicDecrease ==
    [][BeanCount' < BeanCount]_vars

(* Eventually only one bean remains. *)
EventuallyTerminates ==
    <>(ENABLED Termination)

(* The parity of the number of white beans never changes. *)
LoopInvariant ==
    [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

(* If the initial number of white beans is even, the final bean is black; *)
(* if it is odd, the final bean is white.                                 *)
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>[](can.black = 1 /\ can.white = 0)
    ELSE <>[](can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventuallyTerminates
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis

=============================================================================
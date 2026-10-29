---------------------------- MODULE CoffeeCan ----------------------------
(***************************************************************************)
(* The Coffee Can problem. A can holds black and white beans. While more   *)
(* than one bean remains, two beans are removed:                           *)
(*   - two black beans: discard both, put one black bean back              *)
(*   - two white beans: discard both, put one black bean back              *)
(*   - one of each:     discard the black one, put the white one back      *)
(* When only one bean remains, the system stutters (terminates).           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

BeanCount == can.black + can.white

-----------------------------------------------------------------------------
TypeInvariant == can \in Can

Init ==
    /\ can \in Can
    /\ BeanCount \in 1..MaxBeanCount

(* Two black beans removed; one black bean put back. *)
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Two white beans removed; one black bean put back. *)
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

(* One black and one white removed; the white bean is put back. *)
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Only one bean remains: stutter. *)
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
(* Every non-stuttering step strictly decreases the number of beans. *)
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

(* Eventually only one bean remains, and it stays that way. *)
EventuallyTerminates == <>[](ENABLED Termination)

(* The parity of the number of white beans is preserved by every step. *)
LoopInvariant == [][(can.white % 2 = 0) <=> (can'.white % 2 = 0)]_vars

(* The final bean is black iff the initial number of white beans is even. *)
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
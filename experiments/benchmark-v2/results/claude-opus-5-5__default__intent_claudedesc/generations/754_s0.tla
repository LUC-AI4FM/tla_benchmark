------------------------------ MODULE CoffeeCan ------------------------------
(***************************************************************************)
(* The Coffee Can Bean Problem.                                           *)
(*                                                                         *)
(* A coffee can holds some black and white beans (at least one bean in     *)
(* total).  Until a single bean remains, two beans are drawn at random:    *)
(*   - same color      : discard both and add one black bean;              *)
(*   - different colors: discard the black bean, return the white one.     *)
(* Each step removes exactly one bean, so the process terminates.          *)
(*                                                                         *)
(* Key insight: the parity of the number of white beans never changes.     *)
(* So the last bean is white iff the initial number of white beans is odd. *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS MaxBlackBeans, MaxWhiteBeans

ASSUME /\ MaxBlackBeans \in Nat
       /\ MaxWhiteBeans \in Nat
       /\ MaxBlackBeans + MaxWhiteBeans >= 1

VARIABLE can

vars == <<can>>

Can == [black : Nat, white : Nat]

BeanCount == can.black + can.white

TypeOK == can \in Can

Init ==
    can \in {c \in [black : 0..MaxBlackBeans, white : 0..MaxWhiteBeans] :
                 c.black + c.white >= 1}

(* Two black beans drawn: discard both, add one black => net one black removed *)
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Two white beans drawn: discard both, add one black *)
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

(* One of each drawn: discard the black, return the white *)
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

(* Explicit terminal stuttering step, so TLC does not report deadlock *)
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
(* Safety: the can is never empty *)
NonEmpty == BeanCount >= 1

(* Monotonic progress: every non-stuttering step strictly decreases the count *)
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

(* Guaranteed termination *)
EventuallyTerminates == <>(BeanCount = 1)

(* Once terminated, stay terminated *)
TerminationIsStable == [](BeanCount = 1 => [](BeanCount = 1))

(* Loop invariant: the parity of the white bean count is preserved by every step *)
LoopInvariant == [][(can.white % 2) = (can'.white % 2)]_vars

(* Final-state hypothesis: the color of the last bean is determined solely   *)
(* by the parity of the initial number of white beans.                       *)
(*   initial white odd  => last bean white                                   *)
(*   initial white even => last bean black                                   *)
FinalBeanIsWhite == BeanCount = 1 /\ can.white = 1
FinalBeanIsBlack == BeanCount = 1 /\ can.black = 1

Hypothesis ==
    \A w \in 0..MaxWhiteBeans :
        (can.white = w) =>
            /\ (w % 2 = 1) => <>[]FinalBeanIsWhite
            /\ (w % 2 = 0) => <>[]FinalBeanIsBlack

(* Safety form of the hypothesis, quantified over the initial white count *)
HypothesisSafety ==
    \A w \in 0..MaxWhiteBeans :
        (can.white = w) =>
            [](BeanCount = 1 => ((can.white = 1) <=> (w % 2 = 1)))

THEOREM Spec => []TypeOK
THEOREM Spec => []NonEmpty
THEOREM Spec => MonotonicDecrease
THEOREM Spec => LoopInvariant
THEOREM Spec => EventuallyTerminates
THEOREM Spec => Hypothesis
THEOREM Spec => HypothesisSafety
=============================================================================
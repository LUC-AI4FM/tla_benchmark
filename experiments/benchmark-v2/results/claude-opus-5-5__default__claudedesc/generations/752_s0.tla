------------------------------ MODULE ApaCoffeeCan ------------------------------
(***************************************************************************)
(* Wrapper that adds Apalache type annotations to the CoffeeCan spec. The  *)
(* CoffeeCan definitions are inlined here so that this module passes SANY  *)
(* on its own. The annotations are written as comments, so the core logic  *)
(* contains no tool-specific syntax.                                       *)
(*                                                                         *)
(* Configuration: MaxBeanCount = 5, SPECIFICATION Spec,                    *)
(*                INVARIANT TypeInvariant                                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES
    \* @type: [black: Int, white: Int];
    can

vars == << can >>

\* The set of all possible cans
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Safety: the can is always a record of two non-negative bean counts
TypeInvariant == can \in [black : Nat, white : Nat]

\* Number of beans currently in the can
BeanCount == can.black + can.white

\* Start with a can holding between 1 and MaxBeanCount beans
Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Two black beans picked: throw both out, put one black bean back
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Two white beans picked: throw both out, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* One black and one white bean picked: throw out black, put white back
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Exactly one bean remains: the algorithm terminates
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars

\* Variant of Spec with weak fairness, used for checking liveness
FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

\* Each non-terminating step strictly reduces the number of beans
MonotonicDecrease == [][BeanCount' < BeanCount]_vars

\* Liveness: the algorithm eventually terminates (under FairSpec)
EventuallyTerminates == <>(ENABLED Termination)

\* Loop invariant: the parity of the white bean count is preserved
LoopInvariant == [][can.white % 2 = 0 <=> can.white' % 2 = 0]_vars

\* The color of the last bean depends on the initial parity of white beans
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM FairSpec => EventuallyTerminates
=============================================================================
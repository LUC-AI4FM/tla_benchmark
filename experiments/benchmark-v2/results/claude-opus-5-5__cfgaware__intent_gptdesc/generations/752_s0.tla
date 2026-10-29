---------------------------- MODULE CoffeeCan ----------------------------
(***************************************************************************)
(* The "coffee can" bean-removal process.                                  *)
(*                                                                         *)
(* A can holds black and white beans. While at least two beans remain,     *)
(* two beans are drawn nondeterministically:                               *)
(*   - same color (two black or two white): remove both, return one black; *)
(*   - different colors: remove both, return one white.                    *)
(* The process stops when at most one bean remains.                        *)
(*                                                                         *)
(* Net effect of each draw:                                                *)
(*   BB : black - 1                                                        *)
(*   WW : white - 2, black + 1                                             *)
(*   BW : black - 1 (the white bean is returned)                           *)
(* So the number of white beans changes by 0 or -2, and its parity never   *)
(* changes.                                                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCountAssumption == MaxBeanCount \in Nat

VARIABLES
    black,      \* number of black beans currently in the can
    white,      \* number of white beans currently in the can
    initWhite   \* number of white beans in the initial state (ghost variable)

vars == <<black, white, initWhite>>

BeanCount == black + white

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ black \in 0..(2 * MaxBeanCount)
    /\ white \in 0..MaxBeanCount
    /\ initWhite \in 0..MaxBeanCount

Init ==
    /\ black \in 0..MaxBeanCount
    /\ white \in 0..MaxBeanCount
    /\ initWhite = white

-----------------------------------------------------------------------------
(* Two black beans drawn: remove both, return one black. *)
PickSameBlack ==
    /\ black >= 2
    /\ black' = black - 1
    /\ UNCHANGED <<white, initWhite>>

(* Two white beans drawn: remove both, return one black. *)
PickSameWhite ==
    /\ white >= 2
    /\ white' = white - 2
    /\ black' = black + 1
    /\ UNCHANGED initWhite

(* One black and one white drawn: remove both, return one white. *)
PickDifferent ==
    /\ black >= 1
    /\ white >= 1
    /\ black' = black - 1
    /\ UNCHANGED <<white, initWhite>>

Pick == PickSameBlack \/ PickSameWhite \/ PickDifferent

Terminated == BeanCount <= 1

(* Once terminated, the system only stutters (avoids spurious deadlock). *)
Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next == Pick \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

(* The parity of the white-bean count is preserved. *)
WhiteParityInvariant == white % 2 = initWhite % 2

(* A remaining single bean is white iff the initial white count was odd. *)
FinalStateCharacterization ==
    (Terminated /\ BeanCount = 1) =>
        ((white = 1) <=> (initWhite % 2 = 1))

(* If the initial white count was odd, a white bean always remains. *)
OddWhiteNeverVanishes ==
    (initWhite % 2 = 1) => (white >= 1)

(* Each Pick step strictly decreases the bean count by exactly one. *)
BeanCountDecreases ==
    [][Pick => BeanCount' = BeanCount - 1]_vars

(* The parity of white beans is preserved by every step (action form). *)
ParityStepProperty ==
    [][white' % 2 = white % 2]_vars

(* Termination: eventually at most one bean remains, and it stays so. *)
Termination == <>Terminated

StableTermination == <>[]Terminated

THEOREM Spec => []TypeInvariant
THEOREM Spec => []WhiteParityInvariant
THEOREM Spec => []FinalStateCharacterization
THEOREM Spec => Termination
=============================================================================
---------------------------- MODULE CoffeeCan ----------------------------
(***************************************************************************)
(* The classic "coffee can" problem.                                       *)
(*                                                                         *)
(* A finite can holds black and white beans, and at least one bean to      *)
(* begin with. While at least two beans remain, the system takes two beans *)
(* out, chosen nondeterministically, and updates the can as follows:       *)
(*   - Both beans the same color: discard both and put in one black bean.  *)
(*   - Beans of different colors: put the white bean back, discard the     *)
(*     black bean.                                                         *)
(* The process stops when fewer than two beans remain, which means exactly *)
(* one bean remains.                                                       *)
(*                                                                         *)
(* Only counts are modeled. The variable initW is a ghost (history)        *)
(* variable. It records the initial number of white beans so that we can   *)
(* state the final-state characterization.                                 *)
(*                                                                         *)
(* Fairness: weak fairness on Next rules out stuttering forever while a    *)
(* bean-removal step is enabled. The initial total is bounded by the       *)
(* finite constant MaxBeans. Each step lowers the total by exactly one, so *)
(* a finite start makes termination meaningful and guaranteed.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeans          \* upper bound on the finite initial total

ASSUME MaxBeansAssump == MaxBeans \in Nat /\ MaxBeans >= 1

VARIABLES b,      \* number of black beans
          w,      \* number of white beans
          initW   \* ghost: initial number of white beans

vars == <<b, w, initW>>

Total == b + w

TypeOK ==
    /\ b \in Nat
    /\ w \in Nat
    /\ initW \in Nat

-----------------------------------------------------------------------------
(* Initial condition: any nonzero finite total number of beans.            *)
Init ==
    /\ b \in 0..MaxBeans
    /\ w \in 0..MaxBeans
    /\ b + w \in 1..MaxBeans
    /\ initW = w

(* Two black beans are drawn: discard both, add one black bean.            *)
PickBlackBlack ==
    /\ b >= 2
    /\ b' = b - 1
    /\ w' = w
    /\ UNCHANGED initW

(* Two white beans are drawn: discard both, add one black bean.            *)
PickWhiteWhite ==
    /\ w >= 2
    /\ w' = w - 2
    /\ b' = b + 1
    /\ UNCHANGED initW

(* One black and one white bean are drawn: return the white bean and       *)
(* discard the black one.                                                  *)
PickBlackWhite ==
    /\ b >= 1
    /\ w >= 1
    /\ b' = b - 1
    /\ w' = w
    /\ UNCHANGED initW

Step == PickBlackBlack \/ PickWhiteWhite \/ PickBlackWhite

Terminated == Total < 2

(* Explicit stuttering in the terminal state, so TLC does not report a     *)
(* deadlock.                                                               *)
Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties.                                                      *)

(* The can never becomes empty.                                            *)
NonEmpty == Total >= 1

(* The total never goes above the bound.                                   *)
Bounded == Total <= MaxBeans

(* Parity invariant: the parity of the white count never changes.          *)
WhiteParityInv == (w % 2) = (initW % 2)

(* Before termination, every transition lowers the total by exactly one.   *)
DecreaseByOne ==
    [][ ~Terminated => (b' + w') = (b + w) - 1 ]_vars

(* Each transition keeps the parity of the white count.                    *)
ParityPreserved ==
    [][ (w' % 2) = (w % 2) ]_vars

(* Final-state characterization: once one bean remains, its color is      *)
(* fixed by the initial parity of the white count. Even means black, odd   *)
(* means white.                                                            *)
FinalColorInv ==
    Terminated =>
        /\ Total = 1
        /\ ((initW % 2 = 0) => (b = 1 /\ w = 0))
        /\ ((initW % 2 = 1) => (b = 0 /\ w = 1))

-----------------------------------------------------------------------------
(* Liveness properties.                                                    *)

(* Termination: the process always reaches a state with exactly one bean.  *)
Termination == <>(Total = 1)

(* After that, it stays with one bean of the predicted color.              *)
FinalOutcome ==
    <>[]( /\ Total = 1
          /\ w = initW % 2
          /\ b = 1 - (initW % 2) )

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []NonEmpty
THEOREM Spec => []Bounded
THEOREM Spec => []WhiteParityInv
THEOREM Spec => DecreaseByOne
THEOREM Spec => ParityPreserved
THEOREM Spec => []FinalColorInv
THEOREM Spec => Termination
THEOREM Spec => FinalOutcome
=============================================================================
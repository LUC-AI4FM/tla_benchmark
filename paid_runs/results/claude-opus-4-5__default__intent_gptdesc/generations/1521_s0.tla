---------------------------- MODULE CoffeeCan ----------------------------
(**************************************************************************)
(* Model of the classic "Coffee Can" problem by David Gries.              *)
(* A container holds black and white beans. Repeatedly remove two beans:  *)
(* - If same color: discard both, add one black bean                      *)
(* - If different colors: return white, discard black                     *)
(* Process continues until one bean remains.                              *)
(**************************************************************************)

EXTENDS Naturals

CONSTANTS MaxBeans  \* Finite upper bound on initial total beans

ASSUME MaxBeans \in Nat /\ MaxBeans >= 1

VARIABLES black, white

vars == <<black, white>>

(**************************************************************************)
(* Helper definitions                                                     *)
(**************************************************************************)

Total == black + white

Terminated == Total < 2

WhiteParity == white % 2

(**************************************************************************)
(* Type invariant                                                         *)
(**************************************************************************)

TypeOK == /\ black \in Nat
          /\ white \in Nat
          /\ Total <= MaxBeans

(**************************************************************************)
(* Initial state: any nonzero finite total number of beans                *)
(**************************************************************************)

Init == /\ black \in 0..MaxBeans
        /\ white \in 0..MaxBeans
        /\ Total >= 1
        /\ Total <= MaxBeans

(**************************************************************************)
(* Transition: Remove two black beans, add one black bean                 *)
(* Net effect: black decreases by 1, white unchanged                      *)
(**************************************************************************)

RemoveTwoBlack == /\ black >= 2
                  /\ black' = black - 1
                  /\ white' = white

(**************************************************************************)
(* Transition: Remove two white beans, add one black bean                 *)
(* Net effect: white decreases by 2, black increases by 1                 *)
(**************************************************************************)

RemoveTwoWhite == /\ white >= 2
                  /\ white' = white - 2
                  /\ black' = black + 1

(**************************************************************************)
(* Transition: Remove one black and one white, return white               *)
(* Net effect: black decreases by 1, white unchanged                      *)
(**************************************************************************)

RemoveOneEach == /\ black >= 1
                 /\ white >= 1
                 /\ black' = black - 1
                 /\ white' = white

(**************************************************************************)
(* Combined next-state relation (nondeterministic choice)                 *)
(**************************************************************************)

Next == \/ RemoveTwoBlack
        \/ RemoveTwoWhite
        \/ RemoveOneEach

(**************************************************************************)
(* Stuttering allowed only when terminated                                *)
(**************************************************************************)

Stutter == /\ Terminated
           /\ UNCHANGED vars

(**************************************************************************)
(* Full next-state relation including termination stuttering              *)
(**************************************************************************)

NextOrStutter == Next \/ Stutter

(**************************************************************************)
(* Fairness: Weak fairness on all transitions to ensure progress          *)
(* This rules out pathological infinite deferral of enabled transitions   *)
(**************************************************************************)

Fairness == /\ WF_vars(RemoveTwoBlack)
            /\ WF_vars(RemoveTwoWhite)
            /\ WF_vars(RemoveOneEach)

(**************************************************************************)
(* Complete specification with fairness                                   *)
(**************************************************************************)

Spec == Init /\ [][NextOrStutter]_vars /\ Fairness

(**************************************************************************)
(* SAFETY PROPERTIES                                                      *)
(**************************************************************************)

(**************************************************************************)
(* Safety: Every non-stuttering transition decreases total by exactly 1   *)
(**************************************************************************)

DecreasesBy1 == [][Total' = Total - 1 \/ UNCHANGED vars]_vars

(**************************************************************************)
(* Safety: Total count is always non-negative and bounded                 *)
(**************************************************************************)

TotalBounded == Total >= 0 /\ Total <= MaxBeans

(**************************************************************************)
(* INVARIANT: Parity of white beans is preserved                          *)
(* This is the key insight of the coffee can problem                      *)
(**************************************************************************)

ParityPreserved == [][white' % 2 = white % 2 \/ UNCHANGED vars]_vars

(**************************************************************************)
(* Inductive invariant for parity preservation                            *)
(* The parity of white beans equals the initial parity                    *)
(**************************************************************************)

\* We track that white parity never changes during execution
\* This is verified by checking ParityPreserved as a temporal property

(**************************************************************************)
(* TERMINATION                                                            *)
(**************************************************************************)

(**************************************************************************)
(* Termination: Eventually exactly one bean remains                       *)
(**************************************************************************)

TerminationReached == <>(Total = 1)

(**************************************************************************)
(* Once terminated, we stay terminated (stability)                        *)
(**************************************************************************)

TerminationStable == [](Terminated => []Terminated)

(**************************************************************************)
(* FINAL STATE CHARACTERIZATION                                           *)
(**************************************************************************)

(**************************************************************************)
(* If initial white count is even, final bean is black                    *)
(* If initial white count is odd, final bean is white                     *)
(**************************************************************************)

\* The final state with one bean:
FinalStateBlack == (Total = 1) /\ (black = 1) /\ (white = 0)
FinalStateWhite == (Total = 1) /\ (black = 0) /\ (white = 1)

\* Combined with parity preservation:
\* - Even white parity (0 mod 2) means final bean is black (0 white beans)
\* - Odd white parity (1 mod 2) means final bean is white (1 white bean)

FinalColorDeterminedByParity == 
    [](Total = 1 => ((white % 2 = 0 => FinalStateBlack) /\
                     (white % 2 = 1 => FinalStateWhite)))

(**************************************************************************)
(* Alternative formulation: at termination, white count equals its parity *)
(**************************************************************************)

FinalWhiteEqualsParity == [](Total = 1 => white = white % 2)

(**************************************************************************)
(* COMBINED CORRECTNESS PROPERTIES                                        *)
(**************************************************************************)

\* All safety invariants combined
SafetyInvariant == TypeOK /\ TotalBounded

\* Liveness: process terminates with exactly one bean
LivenessProperty == TerminationReached

\* The complete correctness theorem
Correctness == /\ []SafetyInvariant
               /\ DecreasesBy1
               /\ ParityPreserved
               /\ TerminationReached
               /\ FinalColorDeterminedByParity

(**************************************************************************)
(* THEOREMS                                                               *)
(**************************************************************************)

\* Theorem: Spec ensures type correctness
THEOREM Spec => []TypeOK

\* Theorem: Every transition decreases total by 1 (until termination)
THEOREM Spec => DecreasesBy1

\* Theorem: White parity is invariant
THEOREM Spec => ParityPreserved

\* Theorem: Process terminates (requires fairness and finite initial state)
THEOREM Spec => TerminationReached

\* Theorem: Final bean color determined by initial white parity
THEOREM Spec => FinalColorDeterminedByParity

==========================================================================
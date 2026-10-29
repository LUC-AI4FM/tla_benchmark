------------------------------ MODULE CoffeeCan ------------------------------
(***************************************************************************)
(* The classical "coffee can" problem, modelled as an abstract,            *)
(* nondeterministic state machine.  The can holds indistinguishable white  *)
(* and black beans, and only their counts are recorded.                    *)
(*                                                                         *)
(* While at least two beans remain, two beans are drawn                    *)
(* (nondeterministically):                                                 *)
(*   - same colour (two whites): remove both, add one black.               *)
(*   - same colour (two blacks): remove both, add one black.               *)
(*   - different colours: remove both, return the white one.               *)
(* Every step removes exactly one bean.  The process stops when fewer than *)
(* two beans remain.                                                       *)
(*                                                                         *)
(* MaxBeans is a finite bound on the initial total, used for model         *)
(* checking.  The definitions do not depend on its value, so the          *)
(* invariants and the final-state theorem also hold for every natural      *)
(* initial size.                                                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeans

ASSUME MaxBeansAssump == MaxBeans \in Nat /\ MaxBeans >= 1

VARIABLES white,     \* number of white beans in the can
          black,     \* number of black beans in the can
          initWhite  \* ghost variable: the initial number of white beans

vars == <<white, black, initWhite>>

Total == white + black

-----------------------------------------------------------------------------
(* Initial states: any nonempty can whose total is within the bound.       *)

Init == /\ white \in 0..MaxBeans
        /\ black \in 0..MaxBeans
        /\ white + black \in 1..MaxBeans
        /\ initWhite = white

-----------------------------------------------------------------------------
(* Actions.  Each action is enabled only while at least two beans remain   *)
(* and the required beans are present.                                     *)

\* Two white beans drawn: remove both and add one black bean.
TwoWhite ==
    /\ white >= 2
    /\ white' = white - 2
    /\ black' = black + 1
    /\ UNCHANGED initWhite

\* Two black beans drawn: remove both and add one black bean (net -1 black).
TwoBlack ==
    /\ black >= 2
    /\ black' = black - 1
    /\ UNCHANGED <<white, initWhite>>

\* One white and one black drawn: remove both, return the white one.
Mixed ==
    /\ white >= 1
    /\ black >= 1
    /\ black' = black - 1
    /\ UNCHANGED <<white, initWhite>>

Step == TwoWhite \/ TwoBlack \/ Mixed

\* Termination: fewer than two beans remain, so the system only stutters.
Terminated == Total < 2

Done == Terminated /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

TypeOK == /\ white \in Nat
          /\ black \in Nat
          /\ initWhite \in Nat

\* Counts stay nonnegative and the total stays within its initial bound.
NonNegative == white >= 0 /\ black >= 0

Bounded == Total <= MaxBeans

\* The can is never empty.
NonEmpty == Total >= 1

\* Every update decreases the total by exactly one.  Updates happen only
\* before termination, i.e. while Total >= 2.
StepDecreasesTotal ==
    [][ Step => /\ Total >= 2
                /\ white' + black' = Total - 1
                /\ white' \in Nat
                /\ black' \in Nat ]_vars

\* Once terminated, the state never changes.
TerminatedIsStable ==
    [][ Terminated => UNCHANGED <<white, black>> ]_vars

\* Parity invariant: white mod 2 is preserved (state form, via the ghost).
ParityInvariant == white % 2 = initWhite % 2

\* Parity invariant (action form): every transition preserves white mod 2.
ParityPreserved == [][ (white' % 2) = (white % 2) ]_vars

\* Final-state characterization: when exactly one bean remains, its colour
\* is determined by the parity of the initial number of white beans.
FinalStateCorrect ==
    Total = 1 =>
        IF initWhite % 2 = 0
            THEN black = 1 /\ white = 0
            ELSE white = 1 /\ black = 0

\* Inductive invariant that supports a proof for all natural initial sizes.
Inv == /\ TypeOK
       /\ NonEmpty
       /\ ParityInvariant

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)

\* Termination: eventually, and from then on forever, exactly one bean
\* remains.
Termination == <>[](Total = 1)

\* The final bean has the colour predicted by the initial parity.
EventuallyCorrectFinal ==
    <>[]( /\ Total = 1
          /\ IF initWhite % 2 = 0 THEN black = 1 ELSE white = 1 )

-----------------------------------------------------------------------------
(* Theorems (proofs omitted; checked by TLC for finite MaxBeans)           *)

THEOREM Spec => []TypeOK
THEOREM Spec => []NonNegative
THEOREM Spec => []Bounded
THEOREM Spec => []NonEmpty
THEOREM Spec => []Inv
THEOREM Spec => StepDecreasesTotal
THEOREM Spec => TerminatedIsStable
THEOREM Spec => []ParityInvariant
THEOREM Spec => ParityPreserved
THEOREM Spec => []FinalStateCorrect
THEOREM Spec => Termination
THEOREM Spec => EventuallyCorrectFinal
=============================================================================
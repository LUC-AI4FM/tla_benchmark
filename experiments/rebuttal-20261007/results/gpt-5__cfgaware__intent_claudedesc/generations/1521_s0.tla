------------------------------ MODULE CoffeeCan ------------------------------

EXTENDS Naturals

(*
  Coffee Can problem (Dijkstra, Scholten; Gries)
  Variables:
    W     - count of white beans
    B     - count of black beans
    P     - previous total bean count (lagged by one step)
    Par0  - initial parity of white beans (0 if even, 1 if odd), carried unchanged
    First - TRUE only in the initial state; becomes FALSE after the first step
*)

CONSTANT MAX

ASSUME /\ MAX \in Nat
       /\ MAX >= 1

VARIABLES W, B, P, Par0, First

vars == << W, B, P, Par0, First >>

Total == W + B

Init ==
  /\ W \in 0..MAX
  /\ B \in 0..MAX
  /\ Total \in 1..MAX
  /\ P = Total
  /\ Par0 = (W % 2)
  /\ First = TRUE

BothBlack ==
  /\ B >= 2
  /\ W' = W
  /\ B' = B - 1

BothWhite ==
  /\ W >= 2
  /\ W' = W - 2
  /\ B' = B + 1

DifferentColors ==
  /\ W >= 1 /\ B >= 1
  /\ W' = W
  /\ B' = B - 1

Step ==
  /\ Total >= 2
  /\ ( BothBlack \/ BothWhite \/ DifferentColors )
  /\ P' = Total
  /\ Par0' = Par0
  /\ First' = FALSE

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
  Invariants and properties to be checked by TLC:
   - TypeInv: counts are natural and total stays within bounds.
   - DecreaseInv: after the first state, each state reflects a strict decrease of 1 in total.
   - ParityInv: parity of W is preserved across all steps.
   - Termination: eventually exactly one bean remains.
   - TerminalColor: the final color is determined by the initial parity of white beans.
*)

TypeInv ==
  /\ W \in Nat
  /\ B \in Nat
  /\ Total \in 1..MAX

DecreaseInv ==
  \/ First
  \/ P = Total + 1

ParityInv ==
  (W % 2) = Par0

Termination ==
  <> (Total = 1)

TerminalColor ==
  [] ( Total = 1 => IF Par0 = 0
                    THEN /\ W = 0 /\ B = 1
                    ELSE /\ W = 1 /\ B = 0 )

=============================================================================
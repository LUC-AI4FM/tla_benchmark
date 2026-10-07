--------------------------- MODULE CoffeeCan ---------------------------

EXTENDS Naturals, Integers, TLC

CONSTANT Max

VARIABLES can

(*
  Helper definitions
*)
Total(c) == c.b + c.w

OneBean(c) == Total(c) = 1

TypeOK ==
  /\ can \in [b: 0..Max, w: 0..Max]
  /\ 1 <= Total(can)
  /\ Total(can) <= Max

(*
  Initialization: any nonempty can within bounds
*)
Init ==
  /\ can \in [b: 0..Max, w: 0..Max]
  /\ 1 <= Total(can)
  /\ Total(can) <= Max

(*
  Coffee-can removal rules:
    - Two black: remove two black, add one black       => b' = b - 1, w' = w
    - Two white: remove two white, add one black       => b' = b + 1, w' = w - 2
    - One of each: remove one black and one white, add one white => b' = b - 1, w' = w
*)
RemoveBB ==
  /\ can.b >= 2
  /\ can' = [can EXCEPT !.b = @ - 1]

RemoveWW ==
  /\ can.w >= 2
  /\ can' = [can EXCEPT !.b = @ + 1, !.w = @ - 2]

RemoveBW ==
  /\ can.b >= 1
  /\ can.w >= 1
  /\ can' = [can EXCEPT !.b = @ - 1]

Remove == RemoveBB \/ RemoveWW \/ RemoveBW

(*
  Termination stuttering when exactly one bean remains
*)
Terminate ==
  /\ OneBean(can)
  /\ UNCHANGED can

Next == Remove \/ Terminate

Spec == Init /\ [][Next]_can /\ WF_can(Remove)

(*
  Safety invariants
*)
TypeInv == TypeOK

(*
  Monotonic decrease in total bean count:
    - If more than one bean, each step reduces total by exactly 1
    - If exactly one bean, the system stutters
*)
MonotonicTotal ==
  [] (IF Total(can) > 1
      THEN Total(can') = Total(can) - 1
      ELSE Total(can') = Total(can))

(*
  Parity-based loop invariant on white beans:
    - The parity of the white-bean count is preserved by every removal step
*)
WhiteParityStepInv == [] ((can'.w % 2) = (can.w % 2))

(*
  Liveness: eventual termination under weak fairness of Remove
*)
Termination == <> OneBean(can)

(*
  Parity-to-final-color hypothesis:
    - If the initial number of white beans is odd, the final bean is white
    - If the initial number of white beans is even, the final bean is black
*)
FinalColorHypothesis ==
  /\ ((can.w % 2) = 1 => <> (OneBean(can) /\ can.w = 1))
  /\ ((can.w % 2) = 0 => <> (OneBean(can) /\ can.b = 1))

=======================================================================
------------------------------ MODULE CoffeeCan ------------------------------

EXTENDS Naturals, TLC

CONSTANTS
  MAX,        \* maximum total beans (finite-state bound)
  InitWhite,  \* initial number of white beans
  InitBlack   \* initial number of black beans

VARIABLES
  can         \* record: [w: current white count, b: current black count]

(*
  Constant sanity constraints for model checking.
  They restrict constants to a finite, nonempty initial multiset within the bound.
*)
ASSUME
  /\ MAX \in Nat
  /\ InitWhite \in 0..MAX
  /\ InitBlack \in 0..MAX
  /\ InitWhite + InitBlack \in 1..MAX

(****************************************************************)
(* Helpers                                                       *)
(****************************************************************)

Total(c) == c.w + c.b
OneBean  == Total(can) = 1

(****************************************************************)
(* State predicate invariants                                    *)
(****************************************************************)

TypeInv ==
  /\ can \in [w : 0..MAX, b : 0..MAX]
  /\ Total(can) \in 0..MAX

\* Parity-based loop invariant: parity of white beans is preserved.
LoopInv == (can.w % 2) = (InitWhite % 2)

(****************************************************************)
(* Initial state                                                 *)
(****************************************************************)

Init ==
  /\ can = [w |-> InitWhite, b |-> InitBlack]
  /\ TypeInv

(****************************************************************)
(* Actions                                                       *)
(****************************************************************)

\* Remove two whites, put back one black.
TakeWW ==
  /\ Total(can) >= 2
  /\ can.w >= 2
  /\ can' = [can EXCEPT !.w = @ - 2, !.b = @ + 1]

\* Remove two blacks, put back one black.
TakeBB ==
  /\ Total(can) >= 2
  /\ can.b >= 2
  /\ can' = [can EXCEPT !.b = @ - 1]

\* Remove one white and one black, put back one white.
TakeBW ==
  /\ Total(can) >= 2
  /\ can.w >= 1 /\ can.b >= 1
  /\ can' = [can EXCEPT !.b = @ - 1]

Remove == TakeWW \/ TakeBB \/ TakeBW

\* Stuttering at termination (exactly one bean remains).
TermStutter ==
  /\ OneBean
  /\ can' = can

Next == Remove \/ TermStutter

(****************************************************************)
(* Specification and properties                                  *)
(****************************************************************)

\* Weak fairness on removal ensures eventual progress while enabled.
Spec == Init /\ [][Next]_can /\ WF_can(Remove)

\* Monotonic (nonincreasing) total bean count across all steps.
Monotonic == [](Total(can') <= Total(can))

\* Eventual termination under weak fairness.
Termination == <>(OneBean)

\* Hypothesis: the color of the final bean matches the initial white-parity.
\* When OneBean holds, can.w is 0 (black) if InitWhite is even, else 1 (white).
FinalBeanHyp == [](OneBean => can.w = (InitWhite % 2))

=============================================================================
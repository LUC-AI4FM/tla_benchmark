----------------------------- MODULE CoffeeCan -----------------------------
EXTENDS Naturals

(*
  Coffee can process:
  - State: counts of Black and White beans in a finite container.
  - Step: remove two beans nondeterministically; update counts by rule:
      * same color: discard both; add one Black.
          - two Blacks: (B,W) -> (B-1, W)
          - two Whites: (B,W) -> (B+1, W-2)
      * different colors: return the White; discard the Black.
          - one Black, one White: (B,W) -> (B-1, W)
  - Process continues while at least two beans remain.

  This specification uses a fairness assumption WF_vars(Next) to rule out
  infinite stuttering while Next is enabled, ensuring progress to termination.
*)

VARIABLES Black, White, W0

vars == << Black, White, W0 >>

Total == Black + White

TypeOK == /\ Black \in Nat
          /\ White \in Nat
          /\ W0 \in {0, 1}

Init ==
  /\ Black \in Nat
  /\ White \in Nat
  /\ Total >= 1
  /\ W0 = (White % 2)

(*
  Action cases corresponding to the nondeterministic choice of two beans:
  - SameBlack: choose two black beans
  - SameWhite: choose two white beans
  - Diff: choose one black and one white bean
*)
SameBlack ==
  /\ Black >= 2
  /\ Black' = Black - 1
  /\ White' = White

SameWhite ==
  /\ White >= 2
  /\ Black' = Black + 1
  /\ White' = White - 2

Diff ==
  /\ Black >= 1
  /\ White >= 1
  /\ Black' = Black - 1
  /\ White' = White

Next ==
  /\ (SameBlack \/ SameWhite \/ Diff)
  /\ W0' = W0

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

(*
  Invariant: parity of White is preserved by every transition,
  and equals its initial value W0 established in Init.
*)
ParityInv == (White % 2) = W0

ParityPreserved ==
  [] (Next => (White' % 2) = (White % 2))

(*
  Safety: every Next-step strictly decreases the total number of beans by 1.
  (Stuttering steps are allowed by [][Next]_vars but do not satisfy Next.)
*)
Safety ==
  [] (Next => Total' = Total - 1)

(*
  Enabledness characterization: a two-bean step is enabled iff at least two beans remain.
*)
EnabledNextIff ==
  [] ((Total >= 2) <=> ENABLED Next)

(*
  Termination: under the fairness assumption in Spec,
  the process inevitably reaches a state with exactly one bean.
*)
Termination ==
  <> (Total = 1)

(*
  Final-state characterization: when exactly one bean remains,
  its color is determined solely by the initial parity of White.
*)
FinalStateChar ==
  [] ( (Total = 1)
       =>
       /\ ((W0 = 0) => (Black = 1 /\ White = 0))
       /\ ((W0 = 1) => (Black = 0 /\ White = 1))
     )

=============================================================================
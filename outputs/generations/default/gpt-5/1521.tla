----------------------------- MODULE CoffeeCan -----------------------------

EXTENDS Naturals

CONSTANTS Max, InitCan

VARIABLES can

T(c) == c.black + c.white

BeansType == [black : 0..Max, white : 0..Max]

TypeOk(c) == /\ c \in BeansType
             /\ T(c) \in 1..Max

Init ==
  /\ can = InitCan
  /\ TypeOk(can)

BB ==
  /\ can.black >= 2
  /\ can' = [can EXCEPT !.black = @ - 2, !.white = @ + 1]

WW ==
  /\ can.white >= 2
  /\ can' = [can EXCEPT !.white = @ - 2, !.black = @ + 1]

BW ==
  /\ can.black >= 1
  /\ can.white >= 1
  /\ can' = [can EXCEPT !.black = @ - 1, !.white = @]

Draw == BB \/ WW \/ BW

Term ==
  /\ T(can) = 1
  /\ UNCHANGED can

Next ==
  (T(can) > 1 /\ Draw) \/ Term

Spec ==
  /\ Init
  /\ [][Next]_can
  /\ WF_can(Draw)

\* Safety invariants
TypeInv == /\ can \in BeansType
           /\ T(can) \in 1..Max

ParityInv == (can.white % 2) = (InitCan.white % 2)

\* Monotonic decrease of total bean count on nonterminal steps
Decrease == [] (T(can) > 1 => T(can') = T(can) - 1)

\* Eventual termination under weak fairness
Termination == <> (T(can) = 1)

\* Hypothesis: final color determined by initial parity of white beans
FinalColorHypothesis ==
  [] (T(can) = 1 => ((InitCan.white % 2 = 1) <=> (can.white = 1)))

=============================================================================
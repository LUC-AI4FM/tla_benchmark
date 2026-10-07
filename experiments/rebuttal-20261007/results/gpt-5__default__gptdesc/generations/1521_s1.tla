------------------------------ MODULE CoffeeCan ------------------------------

EXTENDS Naturals, Integers, TLC

CONSTANTS
  Max,             \* maximum total number of beans (a natural, >= 1)
  WhiteInitParity  \* the parity (0 or 1) of the initial number of white beans

VARIABLES
  can              \* record: [b: Nat, w: Nat]

\* Helper state functions
Total == can.b + can.w

\* Initialization: choose any initial counts within bounds, with at least one bean,
\* and bind the initial white-parity constant to the initial state's parity.
Init ==
  /\ Max \in Nat
  /\ WhiteInitParity \in {0, 1}
  /\ can \in [b: 0..Max, w: 0..Max]
  /\ Total \in 1..Max
  /\ (can.w % 2) = WhiteInitParity

\* Bean-removal actions (each reduces the total by exactly 1)
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

\* Stuttering termination when exactly one bean remains
Term ==
  /\ Total = 1
  /\ can' = can

\* Step is any proper removal; Next also allows termination stuttering.
Step == RemoveBB \/ RemoveWW \/ RemoveBW
Next == Step \/ Term

Spec == Init /\ [][Next]_can /\ WF_can(Step)

\* Safety invariants and inductive properties

\* Type and bound invariant
TypeInv ==
  /\ can \in [b: 0..Max, w: 0..Max]
  /\ Total \in 1..Max

\* The total number of beans strictly decreases by 1 on any proper removal step
MonotonicDecrease ==
  [] ( Step => (Total' = Total - 1) )

\* Parity of the number of white beans is invariant and equals the initial parity
WhiteParityInv ==
  [] ( (can.w % 2) = WhiteInitParity )

\* Liveness: eventual termination (under the weak fairness included in Spec)
Termination ==
  <> (Total = 1)

\* Hypothesis: the color of the final single bean matches the initial white parity
FinalBeanHypothesis ==
  /\ (WhiteInitParity = 1) => <> ( /\ Total = 1 /\ can.w = 1 )
  /\ (WhiteInitParity = 0) => <> ( /\ Total = 1 /\ can.b = 1 )

=================================
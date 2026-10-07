------------------------------- MODULE CoffeeCan -------------------------------

EXTENDS Naturals

CONSTANTS
  MAX, \* maximum total number of beans (natural)
  B0,  \* initial number of black beans (natural)
  W0   \* initial number of white beans (natural)

VARIABLES can \* single record state variable holding the current counts

\* State functions and helpers
Total == can.b + can.w

IsEven(n) == \E k \in Nat : n = 2*k
SameParity(m, n) == IsEven(m) = IsEven(n)

\* Initialization: fix the initial counts to the provided constants, within bounds
Init ==
  /\ can = [b |-> B0, w |-> W0]
  /\ B0 \in Nat /\ W0 \in Nat /\ MAX \in Nat
  /\ 1 <= B0 + W0
  /\ B0 + W0 <= MAX

\* Actions (enabled only when their preconditions hold)
TwoBlack ==
  /\ can.b >= 2
  /\ can' = [can EXCEPT !.b = @ - 1, !.w = @]

TwoWhite ==
  /\ can.w >= 2
  /\ can' = [can EXCEPT !.b = @ + 1, !.w = @ - 2]

OneEach ==
  /\ can.b >= 1 /\ can.w >= 1
  /\ can' = [can EXCEPT !.b = @ - 1, !.w = @]

\* Termination stuttering action when exactly one bean remains
Terminate ==
  /\ Total = 1
  /\ can' = can

Removal == TwoBlack \/ TwoWhite \/ OneEach

Next == Removal \/ Terminate

\* Full behavior: allow stuttering and require weak fairness for progress
Spec == Init /\ [Next]_can /\ WF_can(Removal)

\* Safety invariants
TypeInv ==
  /\ can \in [b : Nat, w : Nat]
  /\ 0 <= Total /\ Total <= MAX

\* Parity-based loop invariant on the number of white beans
ParityInv == []( SameParity(can.w, W0) )

\* Monotonic decrease of total bean count (strictly decreases while > 1)
Monotone ==
  []( (Total > 1) => (Total' = Total - 1) )

\* Optional nonincreasing form (implied by Monotone and Terminate)
Nonincreasing ==
  []( Total' <= Total )

\* Liveness: eventual termination under weak fairness
Termination == <> (Total = 1)

\* Hypothesis: final bean color determined by parity of initial white count
FinalBeanColor ==
  [] ( Total = 1
       => IF IsEven(W0)
            THEN /\ can.b = 1 /\ can.w = 0
            ELSE /\ can.w = 1 /\ can.b = 0 )

===============================================================================
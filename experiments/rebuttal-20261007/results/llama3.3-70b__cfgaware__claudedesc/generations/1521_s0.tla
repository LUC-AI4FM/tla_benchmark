---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Integers

CONSTANT MaxBeanCount

VARIABLE can

TypeInvariant == can.black \in 0..MaxBeanCount /\ can.white \in 0..MaxBeanCount
MonotonicDecrease == (can' = can) \/ (can.black + can.white > can'.black + can'.white)
LoopInvariant == (can.white % 2 = can'.white % 2)

Termination == can.black + can.white = 1

Next == 
  /\ can' = [can EXCEPT !.black = @ - 1]
  /\ can'.white = can.white
  \/ can' = [can EXCEPT !.black = @ + 1]
  /\ can'.white = can.white - 2
  \/ can' = [can EXCEPT !.black = @ - 1]
  /\ can'.white = can.white + 1
  \/ can' = can

Spec == 
  /\ (can.black \in 1..MaxBeanCount /\ can.white \in 0..MaxBeanCount) 
    \/ (can.black \in 0..MaxBeanCount /\ can.white \in 1..MaxBeanCount)
  /\ can.black + can.white \in 1..MaxBeanCount
  /\ [][Next]_can
  /\ WF_can(Next)

TerminationHypothesis == 
  (can.white % 2 = 0) => <>[](can.black = 1 /\ can.white = 0)
  \/ (can.white % 2 = 1) => <>[](can.black = 0 /\ can.white = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MonotonicDecrease
THEOREM Spec => []LoopInvariant
THEOREM Spec => TerminationHypothesis

=============================================================================
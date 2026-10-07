```
MODULE CoffeeCan
EXTENDS Integers

CONSTANTS MaxBeanCount

VARIABLES can

Init ==
  /\ can.black \in 0..MaxBeanCount
  /\ can.white \in 0..MaxBeanCount
  /\ can.black + can.white \in 1..MaxBeanCount

TwoBlack ==
  /\ can.black > 1
  /\ can' = [can EXCEPT !.black = @.black - 1]

TwoWhite ==
  /\ can.white > 1
  /\ can' = [can EXCEPT !.white = @.white - 2, !.black = @.black + 1]

BlackAndWhite ==
  /\ can.black > 0
  /\ can.white > 0
  /\ can' = [can EXCEPT !.black = @.black - 1]

Termination ==
  /\ can.black + can.white = 1
  /\ can' = can

Next ==
  \/ TwoBlack
  \/ TwoWhite
  \/ BlackAndWhite
  \/ Termination
  \/ can' = can

Spec ==
  Init /\ [][Next]_can
  /\ WF_var(Next)

TypeInvariant ==
  []((can.black \in 0..MaxBeanCount) /\ (can.white \in 0..MaxBeanCount))

MonotonicDecrease ==
  [](Next -> (can'.black + can'.white < can.black + can.white)) \/ (can' = can)

LoopInvariant ==
  [](BlackAndWhite -> (can'.white % 2 = can.white % 2))
  /\ [](TwoBlack -> (can'.white % 2 = can.white % 2))
  /\ [](TwoWhite -> (can'.white % 2 = can.white % 2))

TerminationHypothesis ==
  []((Init /\ can.white % 2 = 0) -> <>((can.black = 1) /\ (can.white = 0)))
  /\ []((Init /\ can.white % 2 = 1) -> <>((can.black = 0) /\ (can.white = 1)))

THEOREM Spec => TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => LoopInvariant
THEOREM Spec => TerminationHypothesis
```
```
MODULE CoffeeCanBeanProblem
EXTENDS Integers

CONSTANTS MaxBeans
VARIABLES state

Init ==
  /\ state = [black |-> 0, white |-> 0]
  /\ state.black \in 0..MaxBeans
  /\ state.white \in 0..MaxBeans
  /\ state.black + state.white > 0

TwoBlack ==
  /\ state.black >= 2
  /\ state' = [state EXCEPT !.black = @.black - 2]
  /\ UNCHANGED [.white]

TwoWhite ==
  /\ state.white >= 2
  /\ state' = [state EXCEPT !.white = @.white - 2]
  /\ UNCHANGED [.black]

OneEach ==
  /\ state.black > 0
  /\ state.white > 0
  /\ state' = [state EXCEPT !.black = @.black - 1, !.white = @.white - 1]
  /\ UNCHANGED <<>>

Stutter ==
  /\ state.black + state.white = 1
  /\ state' = state

Next ==
  \/ TwoBlack
  \/ TwoWhite
  \/ OneEach
  \/ Stutter

Spec == Init /\ [][Next]_state

TypeInvariant == 
  [](state.black \in 0..MaxBeans /\ state.white \in 0..MaxBeans)

MonotonicDecrease == 
  []<>(state.black + state.white > state'.black + state'.white)_(state)

EventualTermination == 
  <>[]<>(state.black + state.white = 1)

WeakFairness ==
  WF_vars(TwoBlack, state) /\ WF_vars(TwoWhite, state) /\ WF_vars(OneEach, state)

ParityInvariant ==
  [](state.white mod 2 = (Init.state).white mod 2)

Hypothesis == 
  <>((state.black + state.white = 1) /\ (IF (Init.state).white mod 2 = 0 THEN state.black = 1 ELSE state.white = 1))

THEOREM Spec => [](TypeInvariant)
THEOREM Spec => [](MonotonicDecrease)
THEOREM Spec => EventualTermination
THEOREM Spec => ParityInvariant
THEOREM Spec => Hypothesis
```
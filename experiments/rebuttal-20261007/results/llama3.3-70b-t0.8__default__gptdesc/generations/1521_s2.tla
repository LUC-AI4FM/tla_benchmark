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
  /\ UNCHANGED white

TwoWhite ==
  /\ state.white >= 2
  /\ state' = [state EXCEPT !.white = @.white - 2]
  /\ UNCHANGED black

OneOfEach ==
  /\ state.black > 0
  /\ state.white > 0
  /\ state' = [state EXCEPT !.black = @.black - 1, !.white = @.white - 1]

Stutter ==
  /\ state.black + state.white = 1
  /\ UNCHANGED state

Next ==
  \/ TwoBlack
  \/ TwoWhite
  \/ OneOfEach
  \/ Stutter

Spec == Init /\ [][Next]_state

TypeInvariant == 
  [](state.black \in Nat /\ state.white \in Nat)

MonotonicDecrease == 
  []<>(state.black + state.white) <= (state' = [state EXCEPT !.black = @.black - 1, !.white = @.white - 1] \/ state' = [state EXCEPT !.black = @.black - 2] \/ state' = [state EXCEPT !.white = @.white - 2])

EventualTermination == 
  <>[]<>(state.black + state.white = 1)

WF_TwoBlack == WF_vars(TwoBlack, state)
WF_TwoWhite == WF_vars(TwoWhite, state)
WF_OneOfEach == WF_vars(OneOfEach, state)

Fairness == WF_TwoBlack /\ WF_TwoWhite /\ WF_OneOfEach

LoopInvariant == 
  [](state.white mod 2 = 0 => <>[]<>(state.black > 0))

Hypothesis == 
  Init /\ [][Next]_state /\ Fairness => []<>(state.black + state.white = 1) /\ (state.white mod 2 = 0 => state.black = 1)

THEOREM Hypothesis => TypeInvariant /\ MonotonicDecrease /\ EventualTermination /\ LoopInvariant
```
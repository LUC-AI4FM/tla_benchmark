---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT MaxBeans

VARIABLE state

state == [black |-> 0, white |-> 0]

TypeInvariant == 
  state.black \in 0..MaxBeans /\ state.white \in 0..MaxBeans

TwoBlack == 
  state.black > 1 /\ 
  state' = [state EXCEPT !.black = @.black - 2]

TwoWhite == 
  state.white > 1 /\ 
  state' = [state EXCEPT !.white = @.white - 2]

OneEach == 
  state.black > 0 /\ state.white > 0 /\ 
  state' = [state EXCEPT !.black = @.black - 1, !.white = @.white - 1]

Termination == 
  (state.black + state.white) = 1 /\ 
  UNCHANGED state

Next == TwoBlack \/ TwoWhite \/ OneEach \/ Termination

Spec == 
  Init /\ [][Next]_state

Fairness == WF_state(Next)

MonotonicDecrease == 
  [](state.black + state.white >= state'.black + state'.white)

EventualTermination == 
  []<>(state.black + state.white = 1)

LoopInvariant == 
  [](state.white \in {0, 2} \/ state'.white \in {0, 2})

Hypothesis == 
  Init /\ [](Next) => 
    (state.white % 2 = 0 => state'.black = 1) /\ 
    (state.white % 2 = 1 => state'.white = 1)

THEOREM Spec => TypeInvariant
THEOREM Spec => MonotonicDecrease
THEOREM Spec => EventualTermination
THEOREM Spec => LoopInvariant
THEOREM Hypothesis

=============================================================================
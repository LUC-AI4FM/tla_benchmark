```
MODULE CoffeeCanBeans
EXTENDS Integers

CONSTANTS MaxBeans

VARIABLES state

Init ==
  /\ state = [black |-> 0, white |-> 0]
  /\ state.black \in 0..MaxBeans
  /\ state.white \in 0..MaxBeans
  /\ state.black + state.white <= MaxBeans

Next ==
  \/ (state.black >= 2) /\ state' = [state EXCEPT!.black = @.black - 2]
  \/ (state.white >= 2) /\ state' = [state EXCEPT!.white = @.white - 2]
  \/ (state.black > 0) /\ (state.white > 0) /\ state' = [state EXCEPT!.black = @.black - 1, .white = @.white - 1]
  \/ (state.black + state.white = 1) /\ state' = state

TypeInvariant ==
  /\ state.black \in Nat
  /\ state.white \in Nat
  /\ state.black + state.white <= MaxBeans

MonotonicDecrease ==
  state'.black + state'.white <= state.black + state.white

EventualTermination ==
  <>(state.black + state.white = 1)

ParityInvariant ==
  (state.white % 2) = (state.white' % 2)

Fairness ==
  WF_vars(Next, state)

Spec ==
  /\ Init
  /\ [][Next]_state
  /\ TypeInvariant
  /\ []MonotonicDecrease
  /\ EventualTermination
  /\ ParityInvariant
  /\ Fairness

THEOREM Spec => [](TypeInvariant ∧ MonotonicDecrease) ∧ EventualTermination
```
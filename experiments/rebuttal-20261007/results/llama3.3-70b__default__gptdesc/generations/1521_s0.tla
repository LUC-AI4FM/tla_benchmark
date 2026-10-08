```
MODULE CoffeeCanBeanProblem
EXTENDS Integers

CONSTANTS MaxBeans
VARIABLES state

Init == (state = [black |-> 0, white |-> 0] /\ state.black + state.white <= MaxBeans)

Next == 
  \/ (state.black >= 2 /\ state' = [state EXCEPT!.black = @ - 2])
  \/ (state.white >= 2 /\ state' = [state EXCEPT!.white = @ - 2])
  \/ (state.black > 0 /\ state.white > 0 /\ state' = [state EXCEPT!.black = @ - 1, .white = @ - 1])
  \/ (state.black + state.white = 1 /\ state' = state)

Spec == Init /\ [][Next]_state

TypeInvariant == state.black \in Nat /\ state.white \in Nat
MonotonicDecrease == state.black + state.white >= state'.black + state'.white
EventualTermination == <>[](state.black + state.white = 1)
WeakFairness == WF_vars(Next, state)
LoopInvariant == IF state.white mod 2 = 0 THEN state' = [state EXCEPT!.white = @ - 2] ELSE state' = [state EXCEPT!.black = @ - 1, .white = @ - 1]
Hypothesis == (Init.state.white mod 2 = 0) => <>(state.black = 1 /\ state.white = 0)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MonotonicDecrease
THEOREM Spec => EventualTermination
THEOREM Spec => WeakFairness
THEOREM Spec => LoopInvariant
THEOREM Spec => Hypothesis
```
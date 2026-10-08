------------------------------- MODULE SimpleStateTransition -------------------------------

CONSTANTS 
    \* Op is a function from states to sets of states.
    Op,
    \* Forty2 is an example constant for demonstration purposes.
    Forty2,
    \* Inv is the invariant set parameter.
    Inv

VARIABLES state

Init == state = 0

Next ==
    /\ \/ \E nextState \in (Op(state) \cap Inv): state' = nextState
       \/ (Op(state) = {} /\ state' = state)

Spec ==
    Init /\ [][Next]_<<state>>

\* Liveness: If there are possible next states, the system can always make a transition.
Liveness ==
    [](Op(state) /= {} => <>[](state' \in Op(state)))

\* Safety: The state is always within the invariant set.
Safety ==
    []<>(state \in Inv)

=============================================================================
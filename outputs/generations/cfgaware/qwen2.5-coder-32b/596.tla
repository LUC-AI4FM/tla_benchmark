------------------------------- MODULE OneVarSystem -------------------------------

CONSTANTS x

VARIABLES state

Init == state = 0

Next ==
    \/ /\ state = 0
       /\ \/ state' = 1
          \/ state' = 2
    \/ /\ state \in {1, 2}
       /\ state' = 0

Spec == Init /\ [][Next]_<<state>> /\ WF_x(Next)

WF_x(f) == <>[]<>(\E s \in {1, 2} : state = s)

EventuallyStabilize ==
    <>(/\ state = 0
        /\ []<>(state = 0))

RepeatedReturnToZero ==
    [](<>[](state = 0))

NegatedProperty ==
    ~<>(/\ state = 1
         /\ []<>(state = 1))

Postcondition(trace) ==
    LET states == { s : <<s>> \in trace }
    IN \/ states = {}
       \/ \/ 0 \notin states
          \/ (\E s \in {1, 2} : s \in states)

=============================================================================
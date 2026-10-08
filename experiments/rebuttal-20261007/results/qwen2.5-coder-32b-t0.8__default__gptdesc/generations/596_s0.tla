----------------------------- MODULE OneVarSystem -----------------------------

EXTENDS Naturals

CONSTANTS InitialValue

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ \/ x' = 1
          \/ x' = 2
    \/ /\ x /= 0
       /\ x' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<x>>
    /\ WF_x(Next)

EventuallyStabilizes == <>[](x = 0 \/ x = InitialValue)

EventualReturnToZero == <>([]<>[x = 0])

NegationOfProperty == NOT EventuallyStabilizes

Postcondition(trace) ==
    LET actions == [n \in DOMAIN trace |-> trace[n].action]
        states  == [n \in DOMAIN trace |-> trace[n].state]
    IN
    /\ Init
    /\ \A n \in DOMAIN actions : states[n] = x \/ states[n]' = x'
    /\ \A n \in DOMAIN actions : actions[n] => Next

=============================================================================
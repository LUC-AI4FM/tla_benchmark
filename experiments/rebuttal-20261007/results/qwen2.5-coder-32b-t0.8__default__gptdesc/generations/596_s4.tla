---- MODULE OneVariableSystem ----

EXTENDS Naturals, TLC

CONSTANTS MaxValue

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' \in {1, 2}
    \/ /\ x /= 0
       /\ x' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<x>>
    /\ WF_x(Next)

InvariantStabilizing ==
    [](x = 0 => <>[](x = 0))

RepeatedReturnToZero ==
    <>([]<>(x = 0))

NegationTemporalProperty ==
    NOT []<>(x = 1 \/ x = 2)

Postcondition ==
    LET trace == <<{step |-> [pc |-> "Init", variables |-> <<<<x, 0>>>>},
                    {step |-> "Next", variables |-> <<<<x, 1>>>>},
                    {step |-> "Next", variables |-> <<<<x, 0>>>>}>>
    IN
        \A i \in DOMAIN trace :
            /\ i = 1 => (trace[i].step = "Init" /\ trace[i].variables[1][2] = 0)
            /\ i > 1 => (trace[i].step = "Next" /\ 
                        ((trace[i].variables[1][2] = 1 /\ trace[i-1].variables[1][2] = 0) \/
                         (trace[i].variables[1][2] = 0 /\ (trace[i-1].variables[1][2] = 1 \/ trace[i-1].variables[1][2] = 2))))

====
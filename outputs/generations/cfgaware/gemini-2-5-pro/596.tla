---- MODULE OneVar ----
EXTENDS Naturals, Sequences, TLC

CONSTANT CounterexampleTrace
ASSUME CounterexampleTrace = << [x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2] >>

VARIABLE x

Init == x = 0

Next == \/ (x = 0 /\ x' \in {1, 2})
        \/ (x # 0 /\ x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

EventuallyStableAwayFrom1Or2 == <>[](x = 0)

EventuallyRepeatedReturnToZero == []<>(x = 0)

NegationOfAProperty == ~EventuallyStableAwayFrom1Or2

Postcondition ==
    LET RECURSIVE IsPrefix(_)
        IsPrefix(trace) ==
            IF Len(trace) = 0
            THEN TRUE
            ELSE x = trace[1].x /\ NEXT IsPrefix(Tail(trace))
    IN ~IsPrefix(CounterexampleTrace)

=============================================================================
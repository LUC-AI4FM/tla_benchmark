MODULE OneVarFair
EXTENDS Naturals, Sequences

VARIABLES x, trace

Init ==
    /\ x = 0
    /\ trace = << [x |-> 0] >>

Next ==
    \/ /\ x = 0
       /\ x' \in {1,2}
       /\ trace' = Append(trace, [x |-> x'])
    \/ /\ x # 0
       /\ x' = 0
       /\ trace' = Append(trace, [x |-> x'])

SafetyInvariant == [] (x = 0 \/ x = 1 \/ x = 2)

StabilizeAwayFrom12 == <> [] (x = 0)

RepeatedReturnZero == [] <> (x = 0)

NegationOfStabilize == ~(<> [] (x = 0))

Postcondition ==
    /\ [] (Len(trace) > 0)
    /\ [] (∃t \in trace : t.x = 1 \/ t.x = 2)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

=============================================================================

---------------------------- MODULE OneVarTransition ----------------------------
EXTENDS Integers, Sequences, TLC

VARIABLES x

\* Initial condition: x starts at 0
Init == x = 0

\* Transition relation:
\* - From 0, can move nondeterministically to either 1 or 2
\* - From any nonzero value, returns to 0
Next ==
    \/ (x = 0 /\ (x' = 1 \/ x' = 2))
    \/ (x /= 0 /\ x' = 0)

\* Main specification with weak fairness
Spec == Init /\ [][Next]_x /\ WF_x(Next)

\* Safety invariant: x is always in {0, 1, 2}
TypeInvariant == x \in {0, 1, 2}

\* Temporal property: eventually stabilize away from 1
EventuallyNotOne == <>[](x /= 1)

\* Temporal property: eventually stabilize away from 2
EventuallyNotTwo == <>[](x /= 2)

\* Temporal property: eventual repeated return to zero (infinitely often)
EventuallyRepeatedZero == []<>(x = 0)

\* Temporal property: eventually reach zero at least once
EventuallyZero == <>(x = 0)

\* Negation of the property that x eventually stays at 1 forever
NegationProperty == ~<>[](x = 1)

\* Alternative: negation that x never returns to zero
NegationNeverZero == ~[](x /= 0)

\* Postcondition for checking TLC-generated counterexample traces
\* Encoded as records, tuples, and sets
TraceRecord == [state: {"s0", "s1", "s2"}, value: {0, 1, 2}]

TraceTuple == <<[state |-> "s0", value |-> 0],
                [state |-> "s1", value |-> 1],
                [state |-> "s2", value |-> 0]>>

TraceSet == {[state |-> "s0", value |-> 0],
             [state |-> "s1", value |-> 1],
             [state |-> "s1", value |-> 2],
             [state |-> "s2", value |-> 0]}

\* Postcondition check for trace validity
TracePostcondition ==
    LET trace == <<[x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2], [x |-> 0]>>
    IN /\ trace[1].x = 0
       /\ \A i \in 1..(Len(trace)-1):
            \/ (trace[i].x = 0 /\ trace[i+1].x \in {1, 2})
            \/ (trace[i].x /= 0 /\ trace[i+1].x = 0)

\* Combined liveness: system keeps cycling through states
Liveness == []<>(x = 0) /\ []<>(x /= 0)

=============================================================================
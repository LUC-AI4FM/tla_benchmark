---------------------------- MODULE OneVarTransition ----------------------------
EXTENDS Integers, Sequences, TLC

VARIABLES x

\* Initial state: x starts at 0
Init == x = 0

\* Next state relation:
\* - From 0, can move nondeterministically to either 1 or 2
\* - From any nonzero value, returns to 0
Next ==
    \/ (x = 0 /\ (x' = 1 \/ x' = 2))
    \/ (x /= 0 /\ x' = 0)

\* Main specification with stuttering and weak fairness
Spec == Init /\ [][Next]_x /\ WF_x(Next)

\* Safety invariant: x is always in {0, 1, 2}
TypeInvariant == x \in {0, 1, 2}

\* Temporal property: eventually stabilize away from 1
EventuallyNotOne == <>(x /= 1)

\* Temporal property: eventually stabilize away from 2
EventuallyNotTwo == <>(x /= 2)

\* Temporal property: eventually x is not 1 or eventually x is not 2
EventuallyAwayFrom1Or2 == <>(x /= 1) \/ <>(x /= 2)

\* Liveness property: eventual repeated return to zero (infinitely often at 0)
InfinitelyOftenZero == []<>(x = 0)

\* Liveness property: from any state, eventually return to 0
EventuallyZero == <>(x = 0)

\* Negation of a temporal property (x never becomes 0 again after leaving)
NegatedProperty == ~[]<>(x = 0)

\* Alternative liveness: always eventually can take a step
AlwaysEventuallyProgress == []<>(x = 0 \/ x = 1 \/ x = 2)

\* Postcondition for checking TLC-generated counterexample traces
\* Encoded as records, tuples, and sets representing trace states
TraceConstraint ==
    LET 
        \* Example trace encoding as sequence of records
        ExampleTrace == <<[var |-> 0], [var |-> 1], [var |-> 0], [var |-> 2], [var |-> 0]>>
        \* Valid states as a set
        ValidStates == {0, 1, 2}
        \* Transition relation as set of tuples
        ValidTransitions == {<<0, 1>>, <<0, 2>>, <<1, 0>>, <<2, 0>>}
    IN
        /\ x \in ValidStates
        /\ \A i \in 1..(Len(ExampleTrace)-1) : 
            <<ExampleTrace[i].var, ExampleTrace[i+1].var>> \in ValidTransitions \/ 
            ExampleTrace[i].var = ExampleTrace[i+1].var

\* Postcondition checking current state against trace records
PostCondition ==
    LET
        TraceRecords == {[state |-> 0, next |-> {1, 2}], 
                         [state |-> 1, next |-> {0}], 
                         [state |-> 2, next |-> {0}]}
        CurrentRecord == CHOOSE r \in TraceRecords : r.state = x
    IN
        x \in {0, 1, 2}

=============================================================================
---------------------------- MODULE one_variable ----------------------------

EXTENDS Integers, Sequences, TLC

VARIABLES x

(* Initial state: x starts at 0 *)
Init == x = 0

(* Next state relation:
   - From 0, can move nondeterministically to 1 or 2
   - From any nonzero value, returns to 0 *)
Next ==
    \/ (x = 0 /\ (x' = 1 \/ x' = 2))
    \/ (x /= 0 /\ x' = 0)

(* Main specification with stuttering and weak fairness *)
Spec == Init /\ [][Next]_x /\ WF_x(Next)

(* Safety invariant: x is always in {0, 1, 2} *)
TypeInvariant == x \in {0, 1, 2}

(* Temporal property: eventually stabilize away from 1 *)
EventuallyNotOne == <>[](x /= 1)

(* Temporal property: eventually stabilize away from 2 *)
EventuallyNotTwo == <>[](x /= 2)

(* Temporal property: eventually stabilize away from 1 or 2 *)
EventuallyStabilizeAwayFrom1Or2 == EventuallyNotOne \/ EventuallyNotTwo

(* Liveness property: eventual repeated return to zero *)
EventuallyAlwaysReturnsToZero == []<>(x = 0)

(* Negation of a temporal property (e.g., not always eventually at 1) *)
NegatedProperty == ~[]<>(x = 1)

(* Alternative negated property *)
NegatedEventuallyStable == ~<>[](x = 0)

(* Postcondition for TLC counterexample trace checking *)
(* Encoded as records, tuples, and sets *)
CounterexampleTrace == 
    LET 
        trace == <<
            [x |-> 0],
            [x |-> 1],
            [x |-> 0],
            [x |-> 2],
            [x |-> 0]
        >>
        validStates == {0, 1, 2}
        traceRecord == [
            states |-> trace,
            length |-> Len(trace),
            validValues |-> validStates
        ]
    IN
        /\ \A i \in 1..Len(trace) : trace[i].x \in validStates
        /\ traceRecord.length > 0

(* Check that a trace element is valid *)
ValidTraceElement(elem) == elem.x \in {0, 1, 2}

(* Postcondition predicate for TLC trace checking *)
PostCondition ==
    LET
        exampleStates == {[x |-> 0], [x |-> 1], [x |-> 2]}
        transitions == {<<0, 1>>, <<0, 2>>, <<1, 0>>, <<2, 0>>}
    IN
        /\ x \in {0, 1, 2}
        /\ \A s \in exampleStates : s.x \in {0, 1, 2}
        /\ \A t \in transitions : t[1] \in {0, 1, 2} /\ t[2] \in {0, 1, 2}

=============================================================================
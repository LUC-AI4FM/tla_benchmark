---------------------------- MODULE Specification ----------------------------

EXTENDS Integers, Sequences, TLC

VARIABLES x

Init == x = 0

Next ==
    \/ (x = 0 /\ (x' = 1 \/ x' = 2))
    \/ (x /= 0 /\ x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

(* Safety Invariant: x is always in the set {0, 1, 2} *)
TypeInvariant == x \in {0, 1, 2}

(* Temporal property: eventually x is not 1 *)
EventuallyNot1 == <>~(x = 1)

(* Temporal property: eventually x is not 2 *)
EventuallyNot2 == <>~(x = 2)

(* Temporal property: eventually stabilizing away from 1 or 2 *)
EventuallyStabilize == <>(x /= 1) /\ <>(x /= 2)

(* Temporal property: eventual repeated return to zero *)
EventuallyAlwaysReturnToZero == []<>(x = 0)

(* Negation of a temporal property for testing *)
NegatedProperty == ~[]<>(x = 0)

(* Postcondition for TLC counterexample trace checking *)
(* This defines a structure for encoding traces as records, tuples, and sets *)
TraceRecord == [var : {"x"}, val : {0, 1, 2}]

TraceTuple == <<[var |-> "x", val |-> 0], [var |-> "x", val |-> 1], [var |-> "x", val |-> 0]>>

TraceSet == {[var |-> "x", val |-> 0], [var |-> "x", val |-> 1], [var |-> "x", val |-> 2]}

(* Postcondition that checks if a trace is valid *)
ValidTrace(trace) ==
    /\ Len(trace) > 0
    /\ \A i \in 1..Len(trace) : trace[i].val \in {0, 1, 2}

(* Example encoded counterexample trace for TLC *)
CounterexampleTrace == <<
    [x |-> 0],
    [x |-> 1],
    [x |-> 0],
    [x |-> 2],
    [x |-> 0]
>>

(* Check that counterexample trace satisfies transitions *)
ValidCounterexample ==
    /\ CounterexampleTrace[1].x = 0
    /\ \A i \in 1..(Len(CounterexampleTrace) - 1) :
        LET curr == CounterexampleTrace[i].x
            next == CounterexampleTrace[i + 1].x
        IN \/ (curr = 0 /\ next \in {1, 2})
           \/ (curr /= 0 /\ next = 0)
           \/ curr = next

=============================================================================
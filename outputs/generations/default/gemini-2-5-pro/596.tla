---- MODULE OneVar ----
EXTENDS Integers, TLC, Sequences

\* A TLC-generated counterexample trace encoded as a tuple of records.
\* The set {1, 2} is used in the Next action.
CexTrace == << [x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2] >>

VARIABLES x

vars == <<x>>

TypeOK == x \in {0, 1, 2}

Init == x = 0

Next == \/ (x = 0 /\ x' \in {1, 2})
        \/ (x /= 0 /\ x' = 0)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The safety invariant that x remains in the set {0, 1, 2}.
Invariant == []TypeOK

\* A liveness property: x eventually stabilizes to a value other than 1 or 2.
EventuallyStable == <>[](x = 0)

\* A liveness property: x eventually returns to zero, infinitely often.
RepeatedReturnToZero == []<>(x = 0)

\* The negation of the EventuallyStable temporal property.
NegProp == ~EventuallyStable

\* A postcondition that checks if the CexTrace constant represents a valid
\* initial segment of a behavior allowed by the specification.
Postcondition ==
    LET State(n) == CexTrace[n]
        Step(s, t) ==
            LET current_x == s.x, next_x == t.x IN
            \/ (current_x = 0 /\ next_x \in {1, 2})
            \/ (current_x /= 0 /\ next_x = 0)
    IN
    /\ Len(CexTrace) > 0
    /\ State(1).x = 0  \* Check Init
    /\ \A i \in 1..(Len(CexTrace) - 1) : Step(State(i), State(i+1)) \* Check Next

=============================================================================
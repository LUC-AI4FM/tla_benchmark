---- MODULE StateMachine ----
EXTENDS Integers, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

\* The set of all possible initial states.
Init ==
    /\ x \in { {1}, {1, 2} }
    /\ y \in { {1, 2}, {1, 2, 3} }

\* The next-state relation. x' is a subset of y, and y is unchanged.
Next ==
    /\ x' \subseteq y
    /\ UNCHANGED y

\* The full specification is safety-only, as requested.
Spec == Init /\ [][Next]_vars

\* -- Predicates for TLC to count --

\* This predicate is true when x is the set {1, 2, 3}.
FullSet == x = {1, 2, 3}

\* This predicate is true if it is possible for a transition from the current
\* state to result in the element 3 being added to x. This requires that
\* 3 is not currently in x, and that 3 is in y (since x' must be a subset
\* of y).
GainThree == (3 \notin x) /\ (3 \in y)

\* -- Assertion on final state counts --

\* This operator uses the TLC module to inspect the state-exploration statistics
\* after model checking is complete. It asserts that the number of distinct
\* states satisfying the named predicates FullSet and GainThree matches the
\* expected counts.
\* This must be checked as a PROPERTY in the TLC model configuration.
StatsAssertion ==
    LET stats == TLCGet("stats")
    IN Assert(   /\ stats["FullSet"] = 1
                 /\ stats["GainThree"] = 4,
                 "Assertion on named predicate counts failed.")

=============================================================================
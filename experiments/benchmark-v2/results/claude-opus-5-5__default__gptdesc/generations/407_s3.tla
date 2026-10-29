---------------------------- MODULE PrintStateMachine ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

\* Initial state: both variables set to 1, plus a diagnostic message.
\* PrintT always evaluates to TRUE, so it only produces output.
Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT("Init: x = 1, y = 1")

\* Assign x nondeterministically from {1, 2, 3}, keep y at 1,
\* and print the generated successor state.
Assign ==
    /\ x' \in {1, 2, 3}
    /\ y' = 1
    /\ PrintT(<<"Next state", x', y'>>)

\* Stutter step: both variables stay the same.
Stutter ==
    UNCHANGED vars

Next ==
    \/ Assign
    \/ Stutter

\* Trivial safety invariant.
Inv == TRUE

\* The description says the original module has no temporal formula.
\* This definition is included only so the module has the required structure.
\* It adds no fairness condition.
Spec == Init /\ [][Next]_vars

==================================================================================
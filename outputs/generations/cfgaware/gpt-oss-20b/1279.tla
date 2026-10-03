------------------------------ MODULE SmallModel ------------------------------

VARIABLE s

\* Parameterized next-state action.
Next(var) == var' \in 0..1 /\ var' > 0

\* Initial state.
Init == s = 23

\* Temporal specification: all steps satisfy the stuttering-closed Next action on s.
Spec == Init /\ [][Next(s)]_s

\* State invariant asserting that s is never zero.
Inv == s # 0

===============================================================================
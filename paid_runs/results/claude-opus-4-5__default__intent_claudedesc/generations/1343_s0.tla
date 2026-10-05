---------------------------- MODULE ConjunctiveInit ----------------------------
\* This module demonstrates how conjunctive initial-state predicates are
\* evaluated together as a simultaneous constraint rather than sequentially.
\* The order of conjuncts does not matter - TLA+ finds values satisfying all
\* constraints at once.

VARIABLES x, y

\* The initial state predicate consists of three conjuncts that must all be
\* satisfied simultaneously. Note that the order does not matter:
\* - y = 0
\* - x = 0  
\* - y = x
\* These are not evaluated sequentially; rather, TLA+ finds an assignment
\* to (x, y) that satisfies all three constraints at the same time.
\* The only solution is x = 0 and y = 0.
Init ==
    /\ y = 0
    /\ x = 0
    /\ y = x

\* After initialization, both variables remain unchanged forever (stuttering).
Next ==
    /\ x' = x
    /\ y' = y

\* The complete specification with stuttering closure
Spec == Init /\ [][Next]_<<x, y>>

--------------------------------------------------------------------------------
\* INVARIANTS (Safety Properties)
--------------------------------------------------------------------------------

\* The only reachable state has x = 0
XIsZero == x = 0

\* The only reachable state has y = 0
YIsZero == y = 0

\* x and y are always equal
XEqualsY == x = y

\* Combined invariant: the system is always in the single valid state
SingleState == x = 0 /\ y = 0

\* Type invariant (assuming integer values around 0)
TypeOK == x \in {0} /\ y \in {0}

--------------------------------------------------------------------------------
\* THEOREMS (for documentation)
--------------------------------------------------------------------------------

\* The specification implies all safety invariants hold
THEOREM Spec => []SingleState

================================================================================
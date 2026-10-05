---------------------------- MODULE ConjunctiveInit ----------------------------
COMMENT(*
  This module demonstrates how conjunctive initial-state predicates are
  evaluated together as a simultaneous constraint rather than sequentially.
  
  The three conjuncts in Init:
    - y = 0
    - x = 0  
    - y = x
  
  All three must be satisfied simultaneously. The order does not matter
  because TLA+ finds values satisfying all constraints at once.
  
  The only reachable state is x = 0 and y = 0.
*)

VARIABLES x, y

\* Initial state predicate with three conjuncts
\* These are evaluated as a simultaneous constraint, not sequentially
Init ==
    /\ y = 0      \* First conjunct: y equals zero
    /\ x = 0      \* Second conjunct: x equals zero
    /\ y = x      \* Third conjunct: y equals x (redundant but illustrative)

\* Next-state relation: both variables remain unchanged forever (stuttering)
Next ==
    /\ x' = x
    /\ y' = y

\* Type invariant showing the only reachable values
TypeInvariant ==
    /\ x = 0
    /\ y = 0

\* The complete specification with stuttering
Spec ==
    /\ Init
    /\ [][Next]_<<x, y>>

\* Safety property: the system does nothing, staying in the initial state
Safety ==
    /\ x = 0
    /\ y = 0

=============================================================================
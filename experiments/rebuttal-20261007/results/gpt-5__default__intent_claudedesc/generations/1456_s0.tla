----------------------------- MODULE SubsetEnabledPossible -----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == << x, y >>

UNIV3 == {1, 2, 3}

Init ==
  /\ x \in SUBSET {1, 2}
  /\ y = UNIV3

Next ==
  /\ y' = y
  /\ x' \subseteq y

\* Action used to test ENABLED with a subset constraint to a singleton.
SingletonAction ==
  /\ y' = y
  /\ x' \subseteq {3}

\* Safety invariants
TypeInv == x \subseteq UNIV3
AlwaysEnabledSingleton == ENABLED SingletonAction
Inv == TypeInv /\ AlwaysEnabledSingleton

\* Actions for TLC’s _POSSIBLE coverage counting
FullSetTrans ==
  /\ y' = y
  /\ x' = y

Gain3Trans ==
  /\ y' = y
  /\ ~(3 \in x)
  /\ 3 \in x'

\* Postcondition asserting exact expected _POSSIBLE counts
\* - There are 8 reachable states total; from each, exactly one transition to x' = y.
\* - From each state with 3 \notin x (4 such states), there are 4 transitions to x' with 3 \in x'.
Post ==
  /\ _POSSIBLE(FullSetTrans) = 8
  /\ _POSSIBLE(Gain3Trans) = 16

Spec == Init /\ [][Next]_vars
========================================================================================
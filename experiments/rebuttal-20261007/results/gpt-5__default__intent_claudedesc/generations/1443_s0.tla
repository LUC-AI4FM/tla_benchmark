------------------------------ MODULE CounterPossible ------------------------------

EXTENDS Naturals, TLC

CONSTANTS Dummy

VARIABLES x

Init ==
  x = 0

Next ==
  \/ /\ x = 0 /\ x' = 1
  \/ /\ x = 1 /\ x' = 2
  \/ /\ x = 2 /\ x' = 0

Spec ==
  Init /\ [][Next]_x

(*
 Safety invariant: the counter always ranges over 0, 1, 2
*)
TypeInv ==
  x \in {0, 1, 2}

(*
 Predicates tracked by TLC's _POSSIBLE feature.
 - Two_POSSIBLE holds in states where x = 2
 - One_POSSIBLE holds in states where x = 1
 - Wrap_POSSIBLE holds on the wrap-around transition 2 -> 0
*)
Two_POSSIBLE ==
  x = 2

One_POSSIBLE ==
  x = 1

Wrap_POSSIBLE ==
  /\ x = 2
  /\ x' = 0

(*
 Liveness properties: each predicate occurs at least once along every behavior.
*)
Live ==
  /\ <> (x = 1)
  /\ <> (x = 2)
  /\ <> Wrap_POSSIBLE

(*
 Postcondition: assert that TLC recorded exactly one witness for each _POSSIBLE
 predicate during model checking. TLC populates the counts retrievable via TLCGet
 under the string key of the operator's name.
*)
PostCondition ==
  /\ TLCGet("Two_POSSIBLE") = 1
  /\ TLCGet("One_POSSIBLE") = 1
  /\ TLCGet("Wrap_POSSIBLE") = 1

===============================================================================
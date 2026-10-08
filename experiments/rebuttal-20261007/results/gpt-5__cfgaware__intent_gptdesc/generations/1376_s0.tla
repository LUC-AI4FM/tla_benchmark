------------------------------ MODULE GrowingRepo ------------------------------

EXTENDS TLC, FiniteSets, Sequences, Naturals

(*
  A repository of distinct data items that can be added over time.
  - Starts empty
  - Supports nondeterministic additions from a fixed finite universe
  - No removals or modifications (monotonic growth)
  - Arbitrary interleavings (stuttering allowed)
*)

CONSTANTS ITEM_UNIVERSE

ASSUME IsFiniteSet(ITEM_UNIVERSE)

VARIABLES items

vars == << items >>

(*
  Initial state: repository is empty.
*)
Init == items = {}

(*
  Action that adds a single new item i from the allowed universe.
*)
Add(i) == 
  /\ i \in ITEM_UNIVERSE \ items
  /\ items' = items \cup {i}

(*
  Next-state relation: add exactly one new allowed item.
  Stuttering is allowed by wrapping this with [][Next]_vars in Spec.
*)
Next == \E i \in ITEM_UNIVERSE : Add(i)

(*
  Full behavior: arbitrary stuttering around Next.
*)
Spec == Init /\ [][Next]_vars

(*
  Optionally strengthen with weak fairness that whenever some add is continuously
  enabled, eventually some add occurs.
*)
AddAny == \E i \in ITEM_UNIVERSE \ items : items' = items \cup {i}
SpecFair == Spec /\ WF_vars(AddAny)

(*
  Safety invariants.
  - Repository contents are always a subset of the allowed universe.
*)
TypeInv == items \subseteq ITEM_UNIVERSE

(*
  "History-style" state invariant:
  The current set can be enumerated as a sequence of distinct allowed items,
  i.e., it arises from successive single-item additions from the universe.
*)
ReachabilityInv ==
  \E n \in Nat :
    \E s \in [1..n -> ITEM_UNIVERSE] :
      /\ \A i, j \in 1..n : i # j => s[i] # s[j]
      /\ items = { s[k] : k \in 1..n }

(*
  Monotonicity as an action property: every non-stuttering step only grows.
*)
MonotoneStep == Next => items \subseteq items'

(*
  Each step is either a stutter or a single allowed addition (redundant given Next,
  provided here as a checkable property).
*)
SingleStepAddition == Next => (\E i \in ITEM_UNIVERSE \ items : items' = items \cup {i})

(*
  Example liveness properties (optional to check in a model):
  - EventuallyAdds(i): a specific item i eventually appears.
  - EventuallyAddsAll: all allowed items eventually appear.
  - MayRemainAbsent: it is possible that some item remains absent forever.
*)
EventuallyAdds(i) == <> (i \in items)
EventuallyAddsAll == \A i \in ITEM_UNIVERSE : <> (i \in items)
MayRemainAbsent == \E i \in ITEM_UNIVERSE : [] ~(i \in items)

===============================================================================
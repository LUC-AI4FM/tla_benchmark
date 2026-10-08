----------------------------- MODULE PersistentTautologyDetector -----------------------------

EXTENDS TLC

CONSTANTS InitVal, Pred
ASSUME InitVal \in BOOLEAN /\ Pred \subseteq BOOLEAN

VARIABLES val

(*
  State predicate representing the "given boolean proposition" evaluated in the current state.
  It is abstractly determined by the constant set Pred.
*)
Prop == val \in Pred

Init == val = InitVal

(*
  No state change is permitted; the single state component is immutable.
*)
Next == UNCHANGED val

(*
  Temporal behavior: the system is initialized once and then remains forever in that state.
*)
Spec == Init /\ [][Next]_val

(*
  Safety invariants
*)
TypeInv == val \in BOOLEAN
FixedInv == val = InitVal

(*
  No-change action and its temporal lifting
*)
NoChange == val' = val
AlwaysNoChange == []NoChange

THEOREM SpecImpliesTypeInv == Spec => []TypeInv

THEOREM SpecImpliesFixedInv == Spec => []FixedInv

THEOREM SpecImpliesAlwaysNoChange == Spec => AlwaysNoChange

(*
  Liveness-derived logical property:
  Whenever the proposition Prop becomes reachable (◇Prop),
  it eventually becomes permanently true thereafter (◇□Prop).
*)
THEOREM StabilityFromReachability == Spec => [](<>Prop => <><>[]Prop)

================================================================================
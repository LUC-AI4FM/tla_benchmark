------------------------------ MODULE MinimalPTLTautology ------------------------------

EXTENDS Naturals

VARIABLES x

vars == << x >>

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(*
  Trivial safety invariant capturing that the single state variable never changes
  from its initial value 0.
*)
Inv == x = 0

(*
  Propositional temporal tautology to be verified:
  If eventually TRUE holds, then eventually always TRUE holds.
*)
Prop == (<>TRUE => <>[]TRUE)

(*
  TLAPS proof (using propositional temporal logic reasoning) of the tautology.
*)
THEOREM Tautology == Prop
PROOF BY PTL QED

(*
  State the tautology as a property of the specification as well,
  so it can be checked by TLC as a PROPERTY.
*)
THEOREM SpecImpliesProp == Spec => Prop
PROOF BY Tautology QED

=============================================================================
---- MODULE SumConstants ----
EXTENDS Naturals

CONSTANTS Foo1, Foo2

ASSUME ConstantsAreNaturals == Foo1 \in Nat /\ Foo2 \in Nat

\* The derived value: the sum of the two declared constants.
Sum == Foo1 + Foo2

\* Value-level property: the sum is a natural number.
SumIsNat == Sum \in Nat

\* The description says the module has no variables, actions or behavior.
\* These definitions exist only to meet the required structure.
\* They place no constraints on any state.
Init == TRUE

Next == FALSE

Spec == Init /\ [][Next]_<<>>

THEOREM SumType == ConstantsAreNaturals => SumIsNat
====
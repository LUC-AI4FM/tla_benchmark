MODULE SubsetReasoning
EXTENDS Naturals, Integers

CONSTANTS SetNames

VARIABLES sets, asserts, globalConsistency

SubsetRel(s1,s2) == sets[s1] \subseteq sets[s2]
NotSubsetRel(s1,s2) == ∃x ∈ sets[s1] : x ∉ sets[s2]

Consistent ==
  ∀a ∈ asserts :
    (a.kind = "SUBSET" => SubsetRel(a.from, a.to)) ∧
    (a.kind = "NOT_SUBSET" => NotSubsetRel(a.from, a.to))

Init ==
  /\ sets = [name \in SetNames |-> {}]
  /\ asserts = {}
  /\ globalConsistency = TRUE

UpdateSet(name, newSet) ==
  LET newSets == [sets EXCEPT ![name] = newSet]
      in
        /\ newSets' = newSets
        /\ asserts' = asserts
        /\ globalConsistency' = TRUE
        /\ Consistent'

AddAssertion(a) ==
  LET newAsserts == asserts ∪ {a}
      in
        /\ sets' = sets
        /\ asserts' = newAsserts
        /\ globalConsistency' = TRUE
        /\ Consistent'

Next ==
  ∃name \in SetNames, newSet ⊆ Int :
    UpdateSet(name, newSet)
  \/ ∃a : a.kind \in {"SUBSET","NOT_SUBSET"} /\ a.from \in SetNames /\ a.to \in SetNames :
    AddAssertion(a)

Spec == Init /\ [][Next]_<<sets, asserts, globalConsistency>>

Safety == Consistent /\ globalConsistency

===============================================================================
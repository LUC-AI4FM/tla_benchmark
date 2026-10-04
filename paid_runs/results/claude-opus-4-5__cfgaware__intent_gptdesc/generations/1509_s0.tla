---------------------------- MODULE spec ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS StateSet, IndexSet, Mapping

VARIABLES state

vars == <<state>>

TypeOK == state \in StateSet

Init == state \in StateSet

Next == state' \in StateSet

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MappingInvariant == \E i \in IndexSet : Mapping[i] = state

SafetyInvariant == MappingInvariant

LivenessProperty == []<><<Next>>_vars

NoDeadlock == ENABLED Next

=======================================================================
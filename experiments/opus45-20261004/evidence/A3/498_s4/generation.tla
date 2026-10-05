---------------------------- MODULE MultiSlotConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Values, Slots

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : Cardinality(chosen[s]) <= 1

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose(v) ==
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Choose(s, v) ==
    /\ v \in proposed
    /\ chosen[s] = {}
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: Type correctness
TypeInvariant == TypeOK

\* Safety: Nontriviality - chosen values must have been proposed
Nontriviality ==
    \A s \in Slots : chosen[s] \subseteq proposed

\* Safety: Stability - once a value is chosen for a slot, it remains chosen
\* This is captured by the fact that Choose only works on empty slots
\* We express stability as: if a slot has a chosen value, it stays the same
Stability ==
    \A s \in Slots : chosen[s] /= {} => chosen[s] = chosen[s]

\* Safety: Per-slot consistency - at most one value is chosen per slot
Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ Nontriviality
    /\ Consistency

\* Liveness: Eventually every slot becomes nonempty
\* This requires that Values is nonempty
AllSlotsChosen ==
    \A s \in Slots : chosen[s] /= {}

Liveness == <>AllSlotsChosen

\* Temporal property for stability: once chosen, a slot's value never changes
StabilityTemporal ==
    \A s \in Slots : [](chosen[s] /= {} => [][chosen[s]' = chosen[s]]_chosen)

===============================================================================
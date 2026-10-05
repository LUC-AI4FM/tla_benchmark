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
    /\ chosen[s] = {}
    /\ v \in proposed
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: Nontriviality - only proposed values can be chosen *)
Nontriviality ==
    \A s \in Slots : chosen[s] \subseteq proposed

(* Safety: Stability - once a value is chosen for a slot, it remains chosen *)
Stability ==
    \A s \in Slots : \A v \in Values :
        (v \in chosen[s]) => [][v \in chosen'[s]]_vars

(* Safety: Per-slot Consistency - at most one value is chosen per slot *)
Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeOK
    /\ Nontriviality
    /\ Consistency

(* Liveness: Eventually every slot becomes nonempty *)
Liveness ==
    \A s \in Slots : <>(chosen[s] /= {})

(* Alternative formulation of stability as an invariant about chosen sets being monotonic *)
StabilityInvariant ==
    \A s \in Slots : chosen[s] /= {} => chosen[s] \subseteq chosen'[s]

===================================================================================
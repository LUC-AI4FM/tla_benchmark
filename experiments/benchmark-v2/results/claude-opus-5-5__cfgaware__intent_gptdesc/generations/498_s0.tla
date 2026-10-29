------------------------- MODULE MultiConsensus -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

ASSUME Values # {} /\ Slots # {}

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : IsFiniteSet(chosen[s])

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose(v) ==
    /\ v \in Values
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Choose(s) ==
    /\ chosen[s] = {}
    /\ \E v \in proposed :
          chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

ProposeSome == \E v \in Values : Propose(v)

Next ==
    \/ ProposeSome
    \/ \E s \in Slots : Choose(s)

Spec == Init /\ [][Next]_vars

LiveSpec ==
    /\ Spec
    /\ WF_vars(ProposeSome)
    /\ \A s \in Slots : WF_vars(Choose(s))

(* Safety properties *)
Nontriviality ==
    \A s \in Slots : chosen[s] \subseteq proposed

Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

Stability ==
    [][\A s \in Slots :
          chosen[s] # {} => chosen'[s] = chosen[s]]_vars

(* Liveness property *)
Liveness ==
    \A s \in Slots : <>(chosen[s] # {})

=============================================================================
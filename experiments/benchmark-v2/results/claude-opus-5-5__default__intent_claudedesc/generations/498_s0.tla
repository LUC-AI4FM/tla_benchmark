------------------------------ MODULE MultiConsensus ------------------------------
(***************************************************************************)
(* Multi-instance consensus over a fixed set of named slots.               *)
(* Values are first proposed into a shared pool. Each slot then chooses    *)
(* exactly one proposed value, and once chosen that value never changes.   *)
(*                                                                         *)
(* Suggested TLC configuration:                                            *)
(*   CONSTANTS Values = {v1, v2}  Slots = {s1, s2}   (model values)        *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeOK                                                      *)
(*   PROPERTIES Nontriviality Stability Consistency Liveness               *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS Values, Slots

ASSUME ValuesNonempty == Values # {}
ASSUME SlotsNonempty  == Slots # {}

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

---------------------------------------------------------------------------------

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

\* Propose a value into the shared pool.
Propose(v) ==
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

\* Choose a proposed value for a slot that has not yet chosen.
Choose(s, v) ==
    /\ chosen[s] = {}
    /\ v \in proposed
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Fairness ==
    /\ WF_vars(Next)
    /\ \A s \in Slots : WF_vars(\E v \in Values : Choose(s, v))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------
(* Safety properties *)

\* Only proposed values may be chosen for any slot.
Nontriviality ==
    [](\A s \in Slots : chosen[s] \subseteq proposed)

\* Once a slot has a chosen value, it never changes.
Stability ==
    \A s \in Slots, v \in Values :
        [](v \in chosen[s] => [](v \in chosen[s]))

\* Each slot has at most one chosen value.
Consistency ==
    [](\A s \in Slots : Cardinality(chosen[s]) <= 1)

(* Liveness property *)

\* Every slot eventually has a chosen value.
Liveness ==
    \A s \in Slots : <>(chosen[s] # {})

---------------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => Nontriviality /\ Stability /\ Consistency
THEOREM Spec => Liveness

=================================================================================
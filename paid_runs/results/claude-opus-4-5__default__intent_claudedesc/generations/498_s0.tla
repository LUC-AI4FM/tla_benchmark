---------------------------- MODULE MultiSlotConsensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

ASSUME ValuesNonempty == Values # {}
ASSUME SlotsNonempty == Slots # {}

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> Values \union {NULL}]

NULL == CHOOSE n : n \notin Values

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> NULL]

Propose(v) ==
    /\ v \in Values
    /\ v \notin proposed
    /\ proposed' = proposed \union {v}
    /\ UNCHANGED chosen

Choose(s, v) ==
    /\ s \in Slots
    /\ v \in Values
    /\ v \in proposed
    /\ chosen[s] = NULL
    /\ chosen' = [chosen EXCEPT ![s] = v]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Fairness ==
    /\ \A v \in Values : WF_vars(Propose(v))
    /\ \A s \in Slots, v \in Values : WF_vars(Choose(s, v))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety Properties *)

(* Nontriviality: No value may be chosen for any slot unless it was previously proposed *)
Nontriviality ==
    \A s \in Slots : chosen[s] # NULL => chosen[s] \in proposed

(* Consistency: Each slot may have at most one chosen value (implicit in functional representation) *)
(* This is actually always true by construction since chosen is a function *)
(* But we express it as: if a slot has a value, that value is unique *)
Consistency ==
    \A s \in Slots : chosen[s] # NULL => 
        \A v \in Values : (chosen[s] = v) => 
            (\A w \in Values : chosen[s] = w => v = w)

(* Stability: Once a slot has a chosen value it must never change *)
Stability == \A s \in Slots : chosen[s] # NULL => [][chosen[s] = chosen'[s]]_vars

(* Liveness: Under fair execution every slot must eventually have a chosen value *)
Liveness == \A s \in Slots : <>(chosen[s] # NULL)

(* Combined Safety Invariant *)
SafetyInv == TypeOK /\ Nontriviality

(* For model checking stability as a temporal property *)
StabilityTemporal == [][\A s \in Slots : chosen[s] # NULL => chosen[s] = chosen'[s]]_vars

===================================================================================
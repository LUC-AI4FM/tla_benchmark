MODULE Consensus

EXTENDS Naturals, Sequences, TLC

CONSTANTS Slots, Values

ASSUME
  /\ Slots /= {}
  /\ Values /= {}

VARIABLES proposals, chosen

(* Type invariant *)
TypeInv == 
  /\ proposals \subseteq Values
  /\ chosen ⊆ Slots × Values

(* Safety invariants *)
Nontriviality == ∀<<s,v>> ∈ chosen : v ∈ proposals

Consistency == ∀<<s1,v1>>, <<s2,v2>> ∈ chosen :
                s1 = s2 ⇒ v1 = v2

Stability == [] (chosen ⊆ chosen')

(* Liveness property *)
Liveness == ∀s ∈ Slots : <> (∃v ∈ Values : <<s,v>> ∈ chosen)

Init ==
  /\ proposals = {}
  /\ chosen = {}

Propose(v) ==
  /\ v ∈ Values
  /\ proposals' = proposals ∪ {v}
  /\ chosen' = chosen

Choose(s, v) ==
  /\ s ∈ Slots
  /\ v ∈ proposals
  /\ ¬(∃v2 ∈ Values : <<s,v2>> ∈ chosen)
  /\ chosen' = chosen ∪ {<<s,v>>}
  /\ proposals' = proposals

Next == 
  (∃v ∈ Values : Propose(v)) \/ 
  (∃s ∈ Slots, v ∈ proposals : Choose(s,v))

ProposeAction == ∃v ∈ Values : Propose(v)
ChooseAction == ∃s ∈ Slots, v ∈ proposals : Choose(s,v)

Spec == Init /\ [][Next]_ <<proposals, chosen>> 
          /\ TypeInv
          /\ Nontriviality
          /\ Consistency
          /\ Stability
          /\ WF/[] ProposeAction
          /\ WF/[] ChooseAction
          /\ Liveness

===============================================================================
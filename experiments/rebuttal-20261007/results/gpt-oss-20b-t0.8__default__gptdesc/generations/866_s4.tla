MODULE FastPaxos
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANTS Agents, Values

VARIABLES proposed, decided

(* Type invariants *)
TypeInvariant ==
  /\ proposed ∈ [Agents -> Values \cup {⊥}]
  /\ decided ∈ Values \cup {⊥}

(* Initialization *)
Init ==
  /\ proposed = [a \in Agents |-> ⊥]
  /\ decided = ⊥

Propose(a, v) ==
  /\ a ∈ Agents
  /\ v ∈ Values
  /\ decided = ⊥
  /\ proposed' = [proposed EXCEPT ![a] = v]
  /\ UNCHANGED decided

FastRound(v) ==
  /\ v ∈ Values
  /\ decided = ⊥
  /\ (∀ a ∈ Agents : proposed[a] = ⊥ \/ proposed[a] = v)
  /\ decided' = v
  /\ UNCHANGED proposed

ClassicRound ==
  /\ decided = ⊥
  /\ LET n == Cardinality(Agents)
       majoritySize == (n + 1) / 2
     IN
       LET chosen == CHOOSE v \in Values :
           Cardinality({a ∈ Agents : proposed[a] = v}) >= majoritySize
       IN
         decided' = chosen
  /\ UNCHANGED proposed

Next ==
  ∃ a ∈ Agents, v ∈ Values : Propose(a, v)
  \/ ∃ v ∈ Values : FastRound(v)
  \/ ClassicRound

(* Safety property: consensus is only on values that have been proposed *)
NonTriviality ==
  decided = ⊥ \/ ∃ a ∈ Agents : proposed[a] = decided

Spec == Init /\ [][Next]_ <<proposed, decided>> /\ TypeInvariant /\ NonTriviality
===============================================================================
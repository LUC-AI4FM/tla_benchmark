------------------------------ MODULE LiveSpec ------------------------------
EXTENDS TLC

CONSTANTS
  Values, Slots, Undecided

VARIABLES Proposed, Decision

(* Type invariant: Proposed values are a subset of the value domain; 
   Decision maps each slot to either Undecided or a proposed value. *)
TypeInv ==
  /\ Proposed \subseteq Values
  /\ Decision \in [Slots -> (Values ∪ {Undecided})]
  /\ \A s \in Slots : Decision[s] = Undecided \/ Decision[s] \in Proposed

(* Initial state: no proposals, all slots undecided *)
Init ==
  /\ Proposed = {}
  /\ Decision = [s \in Slots |-> Undecided]

(* Proposer action: propose a new value v ∈ Values *)
Propose(v) ==
  /\ v \in Values
  /\ Proposed' = Proposed ∪ {v}
  /\ UNCHANGED Decision

(* Chooser action: decide slot s with value v that has been proposed,
   only if the slot is still undecided. *)
Decide(s, v) ==
  /\ s \in Slots
  /\ v \in Proposed
  /\ Decision[s] = Undecided
  /\ Decision' = [Decision EXCEPT ![s] = v]
  /\ UNCHANGED Proposed

(* Next-state relation: either a proposal or a decision *)
Next ==
  \/ ∃ v \in Values : Propose(v)
  \/ ∃ s \in Slots, v \in Proposed : Decide(s, v)

(* Safety invariant: proposed values are from the domain and decisions
   are persistent. *)
SafetyInv ==
  /\ TypeInv
  /\ \A s \in Slots :
        Decision[s] = Undecided \/ Decision[s] \in Proposed

(* Liveness property: every slot eventually gets a decision. *)
Liveness ==
  \A s \in Slots : [](Decision[s] = Undecided => <> (Decision[s] ≠ Undecided))

Spec == Init /\ [][Next]_<<Proposed, Decision>> /\ SafetyInv

=============================================================================
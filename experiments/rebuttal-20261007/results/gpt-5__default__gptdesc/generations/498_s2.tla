----------------------------- MODULE MultiSlotConsensus -----------------------------

EXTENDS FiniteSets

CONSTANTS
  Slots,
  Values

ASSUME /\ IsFiniteSet(Slots) /\ Slots /= {}
       /\ IsFiniteSet(Values) /\ Values /= {}

VARIABLES Proposed, Chosen

vars == << Proposed, Chosen >>

TypeOK ==
  /\ Proposed \subseteq Values
  /\ Chosen \in [Slots -> SUBSET Values]

Init ==
  /\ Proposed = {}
  /\ Chosen = [s \in Slots |-> {}]

ProposeNew ==
  \E v \in Values \ Proposed:
    /\ Proposed' = Proposed \cup {v}
    /\ Chosen' = Chosen

ChooseForEmptySlot ==
  \E s \in Slots:
    /\ Chosen[s] = {}
    /\ \E v \in Proposed:
         /\ Chosen' = [ Chosen EXCEPT ![s] = {v} ]
         /\ Proposed' = Proposed

Next == ProposeNew \/ ChooseForEmptySlot

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Nontriviality ==
  \A s \in Slots: Chosen[s] \subseteq Proposed

PerSlotConsistency ==
  \A s \in Slots:
    \A x \in Chosen[s]: \A y \in Chosen[s]: x = y

Stability ==
  []( \A s \in Slots: Chosen[s] # {} => Chosen'[s] = Chosen[s] )

AllSlotsNonEmpty ==
  \A s \in Slots: Chosen[s] # {}

Liveness ==
  <> AllSlotsNonEmpty

THEOREM Spec => []TypeOK

THEOREM Spec => []Nontriviality

THEOREM Spec => []PerSlotConsistency

THEOREM Spec => Stability

THEOREM Spec => Liveness

=====================================================================================
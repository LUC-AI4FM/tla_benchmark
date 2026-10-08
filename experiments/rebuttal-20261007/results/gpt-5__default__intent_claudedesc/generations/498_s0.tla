------------------------------- MODULE MultiInstanceConsensus -------------------------------

EXTENDS Naturals

CONSTANTS VALUES, SLOTS, None

ASSUME /\ VALUES # {}
       /\ SLOTS  # {}
       /\ None \notin VALUES

VARIABLES proposed, chosen, chosenHist

vars == << proposed, chosen, chosenHist >>

TypeInv ==
  /\ proposed \subseteq VALUES
  /\ chosen \in [SLOTS -> (VALUES \cup {None})]
  /\ chosenHist \in [SLOTS -> SUBSET VALUES]

Init ==
  /\ proposed = {}
  /\ chosen = [s \in SLOTS |-> None]
  /\ chosenHist = [s \in SLOTS |-> {}]

Propose(v) ==
  /\ v \in VALUES
  /\ v \notin proposed
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED << chosen, chosenHist >>

ChooseSlot(s) ==
  /\ s \in SLOTS
  /\ chosen[s] = None
  /\ proposed # {}
  /\ \E v \in proposed:
       /\ chosen' = [chosen EXCEPT ![s] = v]
       /\ chosenHist' = [chosenHist EXCEPT ![s] = @ \cup {v}]
       /\ UNCHANGED proposed

Next ==
  \/ \E v \in VALUES: Propose(v)
  \/ \E s \in SLOTS: ChooseSlot(s)

Fairness ==
  /\ \A v \in VALUES: WF_vars(Propose(v))
  /\ \A s \in SLOTS: WF_vars(ChooseSlot(s))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

Nontriviality ==
  [](\A s \in SLOTS: chosenHist[s] \subseteq proposed)

Stability ==
  \A s \in SLOTS: [] ( (chosen[s] \in VALUES) => chosen'[s] = chosen[s] )

Consistency ==
  [](\A s \in SLOTS:
        \A v1 \in VALUES:
          \A v2 \in VALUES:
            (v1 \in chosenHist[s] /\ v2 \in chosenHist[s]) => v1 = v2)

Liveness ==
  \A s \in SLOTS: <> (chosen[s] \in VALUES)

=============================================================================================
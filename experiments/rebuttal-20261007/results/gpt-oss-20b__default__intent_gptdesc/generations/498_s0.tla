------------------------------ MODULE MultiConsensus ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS ValueDomain, Slots, None

VARIABLES proposed, decision

vars == <<proposed, decision>>

(* Type invariant *)
TypeInvariant ==
  /\ proposed \subseteq ValueDomain
  /\ decision \in [Slots -> (ValueDomain ∪ {None})]
  /\ \A s \in Slots : decision[s] = None \/ decision[s] \in ValueDomain

Init ==
  /\ proposed = {}
  /\ decision \in [Slots -> (ValueDomain ∪ {None})]
  /\ \A s \in Slots : decision[s] = None

Propose(v) ==
  /\ v \in ValueDomain
  /\ v \notin proposed
  /\ proposed' = proposed ∪ {v}
  /\ UNCHANGED decision

Decide(s, v) ==
  /\ s \in Slots
  /\ decision[s] = None
  /\ v \in proposed
  /\ decision' = [decision EXCEPT ![s] = v]
  /\ UNCHANGED proposed

Next == \/ ∃v \in ValueDomain : Propose(v)
      \/ ∃s \in Slots, v \in proposed : Decide(s,v)

(* Safety property *)
Safety ==
  /\ \A s \in Slots :
       (decision[s] = None) \/ (decision[s] \in proposed)

(* Persistence of decisions *)
Persistence ==
  \A s \in Slots : [] (decision[s] = None \/ decision[s] = decision'[s])

(* Liveness property *)
Liveness == ∀s \in Slots : [] <> (decision[s] ≠ None)

Spec == Init /\ [][Next]_vars

ASSERT TypeInvariant
ASSERT Safety
ASSERT Persistence
ASSERT Fairness(Decide)
ASSERT Liveness
=============================================================================
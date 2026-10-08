---------------------------- MODULE FastLock ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES pc, trying, critical, turn

Init ==
  /\ pc = [i \in 1..N |-> "noncritical"]
  /\ trying = {}
  /\ critical = {}
  /\ turn = 1

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "noncritical"
      /\ pc' = [pc EXCEPT ![i] = "trying"]
      /\ UNCHANGED <<trying, critical, turn>>
  \/ \E i \in 1..N :
      /\ pc[i] = "trying"
      /\ trying' = trying \cup {i}
      /\ pc' = pc
      /\ UNCHANGED <<critical, turn>>
  \/ \E i \in 1..N :
      /\ pc[i] = "trying"
      /\ i = turn
      /\ critical' = {i}
      /\ trying' = trying \ {i}
      /\ pc' = [pc EXCEPT ![i] = "critical"]
      /\ turn' = (turn % N) + 1
  \/ \E i \in 1..N :
      /\ pc[i] = "critical"
      /\ critical' = {}
      /\ trying' = trying
      /\ pc' = [pc EXCEPT ![i] = "noncritical"]
      /\ UNCHANGED turn

Invariant ==
  /\ pc \in [1..N -> {"noncritical", "trying", "critical"}]
  /\ trying \subseteq 1..N
  /\ critical \subseteq 1..N
  /\ turn \in 1..N
  /\ Cardinality(critical) <= 1

CondLiveness ==
  <>[]<>(\E i \in 1..N : pc[i] = "critical")

FairSpec ==
  SF_VARIABLES <<pc, trying, critical, turn>>
  /\ WF_VARIABLES(Next, pc)
  /\ WF_VARIABLES(Next, trying)
  /\ WF_VARIABLES(Next, critical)
  /\ WF_VARIABLES(Next, turn)

THEOREM Invariant => []Invariant
THEOREM FairSpec => CondLiveness

=============================================================================
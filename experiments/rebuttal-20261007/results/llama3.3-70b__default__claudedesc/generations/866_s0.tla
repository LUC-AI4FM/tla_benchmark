```tla
MODULE FastPaxos
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Ballots, FastBallots, Quorums, FastQuorums
VARIABLES state, ballot, vote, cValue, decided

Init ==
  /\ state = [r \in Replicas |-> "initial"]
  /\ ballot = [r \in Replicas |-> 0]
  /\ vote = [r \in Replicas |-> <<>>]
  /\ cValue = undef
  /\ decided = <<>>

Next ==
  \/ \E r \in Replicas :
      /\ state[r] = "initial"
      /\ state' = [state EXCEPT ![r] = "fast"]
      /\ ballot' = ballot
      /\ vote' = vote
      /\ cValue' = cValue
      /\ decided' = decided
  \/ \E r \in Replicas :
      /\ state[r] = "fast"
      /\ FastDecide(r)
  \/ \E r \in Replicas :
      /\ state[r] = "classic"
      /\ ClassicDecide(r)

FastDecide(r) ==
  /\ state' = [state EXCEPT ![r] = "decided"]
  /\ ballot' = [ballot EXCEPT ![r] = 1]
  /\ vote' = [vote EXCEPT ![r] = <<1, some v \in Values>>]
  /\ cValue' = undef
  /\ decided' = <<some v \in Values>>

ClassicDecide(r) ==
  /\ state' = [state EXCEPT ![r] = "decided"]
  /\ ballot' = [ballot EXCEPT ![r] = 3]
  /\ vote' = [vote EXCEPT ![r] = <<3, cValue>>]
  /\ cValue' = some v \in Values
  /\ decided' = <<cValue>>

FastTypeOK ==
  /\ state \in [Replicas -> {"initial", "fast", "classic", "decided"}]
  /\ ballot \in [Replicas -> Ballots]
  /\ vote \in [Replicas -> SUBSET <<>>]
  /\ cValue \in Values \cup {undef}
  /\ decided \in SUBSET Values

FastNontriviality ==
  decided \subseteq {v \in Values : \E r \in Replicas : <<some b \in Ballots, v>> \in vote[r]}

PaxosConsistency ==
  Cardinality(decided) <= 1

Spec ==
  /\ Init
  /\ [][Next]_state
  /\ WF_Vars(FastDecide)
  /\ WF_Vars(ClassicDecide)

THEOREM Spec => []FastTypeOK
THEOREM Spec => []FastNontriviality
THEOREM Spec => []PaxosConsistency
```
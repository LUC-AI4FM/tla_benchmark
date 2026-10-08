```
MODULE Paxos
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Ballots
VARIABLES proposed, accepted, promises, decided

Init ==
  /\ proposed = {}
  /\ accepted = [r \in Replicas |-> <<0, nil>>]
  /\ promises = [r \in Replicas |-> {}]
  /\ decided = {}

Next ==
  \/ \E r \in Replicas, b \in Ballots, v \in Values :
    /\ b > 0
    /\ ~ (EXISTS <<b', _>> \in proposed : b' >= b)
    /\ proposed' = proposed \cup {<<b, v>>}
    /\ accepted' = accepted
    /\ promises' = promises
    /\ decided' = decided
  \/ \E r \in Replicas, b \in Ballots :
    /\ b > 0
    /\ <<b, _>> \in proposed
    /\ ~ (EXISTS <<b', _>> \in proposed : b' > b)
    /\ promises' = [s \in Replicas |-> IF s = r THEN {<<b, accepted[s][2]>>} ELSE promises[s]]
    /\ accepted' = accepted
    /\ proposed' = proposed
    /\ decided' = decided
  \/ \E r \in Replicas, b \in Ballots, v \in Values :
    /\ b > 0
    /\ <<b, _>> \in proposed
    /\ ~ (EXISTS <<b', _>> \in proposed : b' > b)
    /\ Card({s \in Replicas : <<b, _>> \in promises[s]}) >= (Card(Replicas) + 1)/2
    /\ v = IF EXISTS <<_, w>> \in Union({promises[s] : s \in Replicas}) : TRUE
           THEN CHOOSE <<_, w>> \in Union({promises[s] : s \in Replicas}) : TRUE
           ELSE v
    /\ accepted' = [s \in Replicas |-> IF s = r THEN <<b, v>> ELSE accepted[s]]
    /\ promises' = promises
    /\ proposed' = proposed
    /\ decided' = decided
  \/ \E b \in Ballots, v \in Values :
    /\ <<b, v>> \in proposed
    /\ Card({s \in Replicas : accepted[s] = <<b, v>>}) >= (Card(Replicas) + 1)/2
    /\ decided' = decided \cup {v}
    /\ accepted' = accepted
    /\ promises' = promises
    /\ proposed' = proposed

Spec ==
  /\ Init
  /\ [][Next]_proposed,accepted,promises,decided
  /\ WF_proposed(Decide)

Decide == 
  \E b \in Ballots, v \in Values :
    /\ <<b, v>> \in proposed
    /\ Card({s \in Replicas : accepted[s] = <<b, v>>}) >= (Card(Replicas) + 1)/2

NonTriviality ==
  decided \subseteq {v \in Values : EXISTS <<_, v>> \in proposed}

Consistency ==
  decided' \subseteq decided
```
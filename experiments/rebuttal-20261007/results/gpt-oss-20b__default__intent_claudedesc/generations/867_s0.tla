MODULE Paxos
EXTENDS Naturals, Sequences

CONSTANTS Replicas, Values, Ballots, Quorums

VARIABLES promisedBallot, acceptedBallot, acceptedValue, decisions

vars == <<promisedBallot, acceptedBallot, acceptedValue, decisions>>

(* Type invariant *)
TypeInvariant ==
  /\ promisedBallot ∈ [Replicas -> Ballots]
  /\ acceptedBallot ∈ [Replicas -> Ballots]
  /\ acceptedValue ∈ [Replicas -> Values ∪ {⊥}]
  /\ decisions ∈ [Ballots -> Values ∪ {⊥}]

(* Initial state *)
Init ==
  /\ promisedBallot = [r \in Replicas |-> 0]
  /\ acceptedBallot = [r \in Replicas |-> 0]
  /\ acceptedValue = [r \in Replicas |-> ⊥]
  /\ decisions = [b \in Ballots |-> ⊥]

(* Helper *)
IsQuorum(Q) == Q ∈ Quorums

Prepare ==
  \E r ∈ Replicas, b ∈ Ballots :
    LET P' == [promisedBallot EXCEPT ![a] = IF promisedBallot[a] < b THEN b ELSE promisedBallot[a]] IN
      /\ promisedBallot' = P'
      /\ UNCHANGED <<acceptedBallot, acceptedValue, decisions>>

Accept ==
  \E r ∈ Replicas, b ∈ Ballots, v ∈ Values :
    /\ \E Q \subseteq Replicas : IsQuorum(Q) /\ \A a ∈ Q : promisedBallot[a] = b
    LET A' == [acceptedBallot EXCEPT ![a] = IF promisedBallot[a] = b THEN b ELSE acceptedBallot[a]]
        V' == [acceptedValue EXCEPT ![a] = IF promisedBallot[a] = b THEN v ELSE acceptedValue[a]] IN
      /\ acceptedBallot' = A'
      /\ acceptedValue' = V'
      /\ UNCHANGED <<promisedBallot, decisions>>

Decide ==
  \E b ∈ Ballots, v ∈ Values :
    /\ decisions[b] = ⊥
    /\ \E Q \subseteq Replicas : IsQuorum(Q) /\ \A a ∈ Q : acceptedBallot[a] = b /\ acceptedValue[a] = v
    /\ decisions' = [decisions EXCEPT ![b] = v]
    /\ UNCHANGED <<promisedBallot, acceptedBallot, acceptedValue>>

Next == Prepare \/ Accept \/ Decide

(* Safety invariant: non-triviality *)
NonTriviality ==
  \A b ∈ Ballots : decisions[b] = ⊥ \/ (\E a ∈ Replicas : acceptedBallot[a] = b /\ acceptedValue[a] = decisions[b])

Spec == Init /\ TypeInvariant /\ [][Next]_vars /\ WF_1(Decide) /\ NonTriviality

END Paxos
--------------------------- MODULE Paxos ---------------------------
EXTENDS Integers, TLC

CONSTANTS Proposers, Acceptors, Values
VARIABLES proposed, accepted, promised, decided

PaxosSpec ==
  /\ proposed \in [Proposers -> (Nat -> Values)]
  /\ accepted \in [Acceptors -> (Nat -> Values)]
  /\ promised \in [Acceptors -> Nat]
  /\ decided \in [Values]

TypeInvariant ==
  /\ proposed \in [Proposers -> (Nat -> Values)]
  /\ accepted \in [Acceptors -> (Nat -> Values)]
  /\ promised \in [Acceptors -> Nat]
  /\ decided \in [Values]

PaxosNontriviality ==
  decided \in {v \in Values : <<p, b>> \in proposed[p][b]}

PaxosConsistency ==
  /\ ~<<decided>> \in [Values]
  /\ \A p1, p2 \in Proposers :
      /\ \A b1, b2 \in Nat :
          /\ (proposed[p1][b1] = proposed[p2][b2])
              => (p1 = p2 /\ b1 = b2)

QuorumInvariant ==
  /\ \E Q \subseteq Acceptors : Cardinality(Q) > (Cardinality(Acceptors) / 2)
  /\ \A a \in Acceptors :
      /\ promised[a] <= Max({b \in Nat : <<a, b>> \in promised})

Prepare(p, b) ==
  /\ ~<<p, b>> \in proposed[p][b]
  /\ proposed' = [proposed EXCEPT ![p][b] = Values]
  /\ accepted' = accepted
  /\ promised' = promised
  /\ decided' = decided

Promise(a, p, b) ==
  /\ <<a, p, b>> \in promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ proposed' = proposed
  /\ accepted' = accepted
  /\ decided' = decided

Accept(p, v, b) ==
  /\ ~<<p, v, b>> \in proposed[p][b]
  /\ proposed' = [proposed EXCEPT ![p][b] = {v}]
  /\ accepted' = [accepted EXCEPT ![a \in Acceptors] = IF (promised[a] <= b) THEN {v} ELSE accepted[a]]
  /\ promised' = promised
  /\ decided' = decided

AcceptDecision(a, v, b) ==
  /\ <<a, v, b>> \in accepted[a]
  /\ decided' = v
  /\ proposed' = proposed
  /\ accepted' = accepted
  /\ promised' = promised

Next ==
  \/ \E p \in Proposers, b \in Nat : Prepare(p, b)
  \/ \E a \in Acceptors, p \in Proposers, b \in Nat : Promise(a, p, b)
  \/ \E p \in Proposers, v \in Values, b \in Nat : Accept(p, v, b)
  \/ \E a \in Acceptors, v \in Values, b \in Nat : AcceptDecision(a, v, b)

PaxosSpec == Init /\ [][Next]_proposed,accepted,promised,decided

THEOREM PaxosTypeOK == TypeInvariant => []TypeInvariant
THEOREM PaxosNontriviality == PaxosSpec => []PaxosNontriviality
THEOREM PaxosConsistency == PaxosSpec => []PaxosConsistency
====================================================================
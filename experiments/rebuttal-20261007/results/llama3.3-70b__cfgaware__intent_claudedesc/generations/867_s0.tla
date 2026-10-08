--------------------------- MODULE Paxos ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT Replicas, Values, Ballots, Quorums
VARIABLE proposed, accepted, decided, promises

PaxosSpec == 
  /\ proposed \in [Replicas -> SUBSET Values]
  /\ accepted \in [Replicas -> (Ballots -> Values)]
  /\ decided \in [Ballots -> Values]
  /\ promises \in [Replicas -> (Ballots -> (Ballots \times Values))]
  /\ Init
  /\ [][Next]_proposed,accepted,decided,promises

Init == 
  /\ proposed = [r \in Replicas |-> {}]
  /\ accepted = [r \in Replicas |-> [b \in Ballots |-> <<>>]]
  /\ decided = [b \in Ballots |-> <<>>]
  /\ promises = [r \in Replicas |-> [b \in Ballots |-> <<>>]]

Next == 
  \/ \E r \in Replicas, b \in Ballots : 
    /\ proposed' = [proposed EXCEPT ![r] = proposed[r] \cup {v} ]
    /\ accepted' = accepted
    /\ decided' = decided
    /\ promises' = [promises EXCEPT ![r] = [promises[r] EXCEPT ![b] = <<b, v>>]]
  \/ \E r \in Replicas, b \in Ballots : 
    /\ proposed' = proposed
    /\ accepted' = [accepted EXCEPT ![r] = [accepted[r] EXCEPT ![b] = v]]
    /\ decided' = decided
    /\ promises' = [promises EXCEPT ![r] = [promises[r] EXCEPT ![b] = <<>>]]
  \/ \E b \in Ballots, Q \in Quorums : 
    /\ proposed' = proposed
    /\ accepted' = accepted
    /\ decided' = [decided EXCEPT ![b] = v]
    /\ promises' = [promises EXCEPT ![r \in Q] = [promises[r] EXCEPT ![b] = <<>>]]

PaxosTypeOK == 
  /\ Replicas \subseteq Nat
  /\ Values \subseteq Nat
  /\ Ballots \subseteq Nat
  /\ Quorums \subseteq SUBSET Replicas
  /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

PaxosNontriviality == 
  []<<\A b \in Ballots : decided[b] \in proposed[Replicas]>>_proposed,accepted,decided,promises

PaxosConsistency == 
  []<<\A b1, b2 \in Ballots : (decided[b1] /= <<>>) /\ (decided[b2] /= <<>>) => decided[b1] = decided[b2]>>_proposed,accepted,decided,promises
====================================================================
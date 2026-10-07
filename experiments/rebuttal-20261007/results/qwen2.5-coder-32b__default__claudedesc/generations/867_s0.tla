------------------------------- MODULE Paxos -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Replicas, Ballots, Values
ASSUME Cardinality(Replicas) = 4
ASSUME Cardinality(Ballots) \geq 1
ASSUME Cardinality(Values) \geq 1

VARIABLES messages, maxBallot, maxVBallot, maxValue, decision

Init == /\ messages = {}
        /\ maxBallot \in [Replicas -> Ballots]
        /\ maxVBallot \in [Replicas -> Ballots]
        /\ maxValue \in [Replicas -> Values]
        /\ decision = <<>>

PaxosPrepare ==
  \E r \in Replicas, b \in Ballots \ {0} :
    /\ b > maxBallot[r]
    /\ messages' = messages \cup {[r, "prepare", b]}
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosPromise ==
  \E r1, r2 \in Replicas, b \in Ballots :
    /\ [r1, "prepare", b] \in messages
    /\ b > maxBallot[r2]
    /\ messages' = messages \cup {[r2, "promise", r1, b, maxVBallot[r2], maxValue[r2]]}
    /\ maxBallot' = [maxBallot EXCEPT ![r2] = b]
    /\ UNCHANGED <<maxVBallot, maxValue, decision>>

PaxosAccept ==
  \E r \in Replicas, q \subseteq Replicas, b \in Ballots, v \in Values :
    /\ Cardinality(q) = 3
    /\ [r, "prepare", b] \in messages
    /\ (\A r2 \in q : [r2, "promise", r, b, _, _] \in messages)
    /\ (v = maxValue[r] \/ (\A r2 \in Replicas : maxVBallot[r2] < b))
    /\ messages' = messages \cup {[r, "accept", b, v]}
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosAccepted ==
  \E r1, r2 \in Replicas, b \in Ballots, v \in Values :
    /\ [r1, "accept", b, v] \in messages
    /\ b >= maxBallot[r2]
    /\ messages' = messages \cup {[r2, "accepted", r1, b, v]}
    /\ maxBallot' = [maxBallot EXCEPT ![r2] = b]
    /\ maxVBallot' = [maxVBallot EXCEPT ![r2] = b]
    /\ maxValue' = [maxValue EXCEPT ![r2] = v]
    /\ UNCHANGED decision

PaxosDecide ==
  \E q \subseteq Replicas, r \in Replicas, b \in Ballots, v \in Values :
    /\ Cardinality(q) = 3
    /\ (\A r2 \in q : [r2, "accepted", r, b, v] \in messages)
    /\ decision' = <<b, v>>
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

Next ==
  PaxosPrepare \/ PaxosPromise \/ PaxosAccept \/ PaxosAccepted \/ PaxosDecide

Spec ==
  /\ Init
  /\ [][Next]_<<messages, maxBallot, maxVBallot, maxValue, decision>>
  /\ WF_[PaxosDecide]_<<messages, maxBallot, maxVBallot, maxValue, decision>>

PaxosNontriviality ==
  \A b \in Ballots, v \in Values :
    /\ <<b, v>> = decision
    -> (\E r \in Replicas : [r, "accept", b, v] \in messages)

PaxosConsistency ==
  \A b1, b2 \in Ballots, v1, v2 \in Values :
    /\ <<b1, v1>> = decision
    /\ <<b2, v2>> = decision
    -> v1 = v2

Liveness == FALSE
=============================================================================
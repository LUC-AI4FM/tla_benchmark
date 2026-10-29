------------------------------- MODULE Paxos -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS any, none

CONSTANTS r1, r2, r3, r4, Replicas

CONSTANTS v1, v2, v3, Values

CONSTANTS Ballots, Quorums

ASSUME /\ Replicas # {}
       /\ Values # {}
       /\ any \notin Values
       /\ none \notin Values
       /\ Ballots \subseteq Nat
       /\ 0 \in Ballots
       /\ \A Q \in Quorums : Q \subseteq Replicas
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

VARIABLES messages,    \* set of all messages sent so far
          decision,    \* decided value, or none
          maxBallot,   \* maxBallot[r]: highest ballot replica r has promised/seen
          maxVBallot,  \* maxVBallot[r]: highest ballot in which r accepted a value
          maxValue     \* maxValue[r]: value r accepted in ballot maxVBallot[r]

vars == <<messages, decision, maxBallot, maxVBallot, maxValue>>

PrepareMsg  == [type : {"Prepare"}, ballot : Ballots]
PromiseMsg  == [type : {"Promise"}, ballot : Ballots, acceptor : Replicas,
                vballot : Ballots, vvalue : Values \cup {none}]
AcceptMsg   == [type : {"Accept"}, ballot : Ballots, value : Values]
AcceptedMsg == [type : {"Accepted"}, ballot : Ballots, value : Values,
                acceptor : Replicas]

Message == PrepareMsg \cup PromiseMsg \cup AcceptMsg \cup AcceptedMsg

PaxosTypeOK ==
    /\ messages \subseteq Message
    /\ decision \in Values \cup {none}
    /\ maxBallot \in [Replicas -> Ballots]
    /\ maxVBallot \in [Replicas -> Ballots]
    /\ maxValue \in [Replicas -> Values \cup {none}]

Send(m) == messages' = messages \cup {m}

PaxosInit ==
    /\ messages = {}
    /\ decision = none
    /\ maxBallot = [r \in Replicas |-> 0]
    /\ maxVBallot = [r \in Replicas |-> 0]
    /\ maxValue = [r \in Replicas |-> none]

\* Phase 1a: a proposer broadcasts a Prepare for ballot b.
Phase1a(b) ==
    /\ b # 0
    /\ ~\E m \in messages : m.type = "Prepare" /\ m.ballot = b
    /\ Send([type |-> "Prepare", ballot |-> b])
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>

\* Phase 1b: acceptor a promises for a higher ballot.
Phase1b(a) ==
    \E m \in messages :
        /\ m.type = "Prepare"
        /\ m.ballot > maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ Send([type |-> "Promise", ballot |-> m.ballot, acceptor |-> a,
                 vballot |-> maxVBallot[a], vvalue |-> maxValue[a]])
        /\ UNCHANGED <<decision, maxVBallot, maxValue>>

\* Phase 2a: proposer with promises from a quorum sends an Accept request.
Phase2a(b) ==
    /\ b # 0
    /\ ~\E m \in messages : m.type = "Accept" /\ m.ballot = b
    /\ \E Q \in Quorums :
        LET S == {m \in messages : /\ m.type = "Promise"
                                   /\ m.ballot = b
                                   /\ m.acceptor \in Q}
        IN
        /\ \A a \in Q : \E m \in S : m.acceptor = a
        /\ \E v \in Values :
            /\ \/ \A m \in S : m.vballot = 0
               \/ \E m \in S : /\ m.vballot # 0
                               /\ m.vvalue = v
                               /\ \A mm \in S : mm.vballot =< m.vballot
            /\ Send([type |-> "Accept", ballot |-> b, value |-> v])
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>

\* Phase 2b: acceptor accepts a value if it has not promised a higher ballot.
Phase2b(a) ==
    \E m \in messages :
        /\ m.type = "Accept"
        /\ m.ballot >= maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.value]
        /\ Send([type |-> "Accepted", ballot |-> m.ballot, value |-> m.value,
                 acceptor |-> a])
        /\ UNCHANGED <<decision>>

\* Decide: a quorum has sent Accepted for the same ballot and value.
PaxosDecide ==
    /\ \E b \in Ballots, v \in Values, Q \in Quorums :
        /\ \A a \in Q : \E m \in messages : /\ m.type = "Accepted"
                                            /\ m.ballot = b
                                            /\ m.value = v
                                            /\ m.acceptor = a
        /\ decision' = v
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

PaxosNext ==
    \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
    \/ \E a \in Replicas : Phase1b(a) \/ Phase2b(a)
    \/ PaxosDecide

PaxosSpec == PaxosInit /\ [][PaxosNext]_vars /\ SF_vars(PaxosDecide)

\* Only proposed values can be decided.
PaxosNontriviality ==
    \/ decision = none
    \/ \E m \in messages : m.type = "Accept" /\ m.value = decision

\* Once decided, the decision never changes.
PaxosConsistency ==
    [][decision # none => decision' = decision]_<<decision>>

PaxosSymmetry == Permutations(Replicas) \cup Permutations(Values)

=============================================================================
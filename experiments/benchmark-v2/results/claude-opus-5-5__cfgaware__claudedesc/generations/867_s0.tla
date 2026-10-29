--------------------------- MODULE Paxos ---------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS any, none, r1, r2, r3, r4, v1, v2, v3

Replicas == {r1, r2, r3, r4}
Values   == {v1, v2, v3}
Ballots  == 0..2
Quorums  == {Q \in SUBSET Replicas : Cardinality(Q) = 3}

VARIABLES messages, maxBallot, maxVBallot, maxValue, decision

vars == <<messages, maxBallot, maxVBallot, maxValue, decision>>

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, from : Replicas, bal : Ballots,
        mbal : Ballots, mval : Values \cup {none}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, from : Replicas, bal : Ballots, val : Values]

PaxosTypeOK ==
  /\ messages \subseteq Messages
  /\ maxBallot  \in [Replicas -> Ballots]
  /\ maxVBallot \in [Replicas -> Ballots]
  /\ maxValue   \in [Replicas -> Values \cup {none}]
  /\ decision   \in Values \cup {none}

PaxosInit ==
  /\ messages   = {}
  /\ maxBallot  = [a \in Replicas |-> 0]
  /\ maxVBallot = [a \in Replicas |-> 0]
  /\ maxValue   = [a \in Replicas |-> none]
  /\ decision   = none

Send(m) == messages' = messages \cup {m}

\* Phase 1a: a proposer broadcasts a prepare for a nonzero ballot
PaxosPrepare ==
  /\ \E b \in Ballots \ {0} :
        Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

\* Phase 1b: an acceptor promises if the ballot exceeds its maximum
PaxosPromise ==
  /\ \E a \in Replicas, m \in messages :
        /\ m.type = "1a"
        /\ m.bal > maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", from |-> a, bal |-> m.bal,
                 mbal |-> maxVBallot[a], mval |-> maxValue[a]])
  /\ UNCHANGED <<maxVBallot, maxValue, decision>>

\* The value forced by a set of 1b messages: the value of the highest
\* previously accepted ballot, or `any' if nothing was accepted.
ForcedValue(S) ==
  IF \A m \in S : m.mbal = 0
    THEN any
    ELSE (CHOOSE m \in S : m.mbal # 0 /\ \A m2 \in S : m.mbal >= m2.mbal).mval

\* Phase 2a: a proposer that collected 1b messages from a quorum
PaxosAccept ==
  /\ \E b \in Ballots \ {0}, Q \in Quorums :
        LET S == {m \in messages : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
        IN
        /\ \A a \in Q : \E m \in S : m.from = a
        /\ ~ \E m \in messages : m.type = "2a" /\ m.bal = b
        /\ LET fv == ForcedValue(S)
           IN \E v \in Values :
                /\ (fv = any) \/ (v = fv)
                /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

\* Phase 2b: an acceptor accepts if the ballot is at least its maximum
PaxosAccepted ==
  /\ \E a \in Replicas, m \in messages :
        /\ m.type = "2a"
        /\ m.bal >= maxBallot[a]
        /\ maxBallot'  = [maxBallot  EXCEPT ![a] = m.bal]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.bal]
        /\ maxValue'   = [maxValue   EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", from |-> a, bal |-> m.bal, val |-> m.val])
  /\ UNCHANGED decision

\* Learning: a quorum sent matching 2b messages for a ballot
PaxosDecide ==
  /\ \E b \in Ballots, Q \in Quorums, v \in Values :
        /\ \A a \in Q :
              [type |-> "2b", from |-> a, bal |-> b, val |-> v] \in messages
        /\ decision' = v
  /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

PaxosNext ==
  \/ PaxosPrepare
  \/ PaxosPromise
  \/ PaxosAccept
  \/ PaxosAccepted
  \/ PaxosDecide

PaxosSpec ==
  /\ PaxosInit
  /\ [][PaxosNext]_vars
  /\ SF_vars(PaxosDecide)

\* Only proposed values can be learnt
PaxosNontriviality ==
  decision # none =>
    \E m \in messages : m.type = "2a" /\ m.val = decision

\* Once a value is decided, it never changes
PaxosConsistency ==
  \A v \in Values : [](decision = v => [](decision = v))

\* Liveness cannot be guaranteed (FLP impossibility)
PaxosLiveness == FALSE

PaxosSymmetry == Permutations(Replicas) \cup Permutations(Values)

=============================================================================
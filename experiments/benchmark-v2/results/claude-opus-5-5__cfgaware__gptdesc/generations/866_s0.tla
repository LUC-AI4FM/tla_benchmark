------------------------------- MODULE FastPaxos -------------------------------
EXTENDS Integers, TLC

CONSTANTS any, none, r1, r2, r3, r4, Replicas, v1, v2, v3, Values,
          Ballots, FastBallots, Quorums, FastQuorums

ASSUME /\ any \notin Values
       /\ none \notin Values
       /\ any # none
       /\ FastBallots \subseteq Ballots
       /\ Ballots \subseteq Nat
       /\ Quorums \subseteq SUBSET Replicas
       /\ FastQuorums \subseteq SUBSET Replicas

VARIABLES messages, decision, maxBallot, maxVBallot, maxValue, cValue

vars == <<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>

NoBallot == -1

ClassicBallots == Ballots \ FastBallots

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Message ==
       [type : {"propose"}, value : Values]
  \cup [type : {"P1a"}, ballot : Ballots]
  \cup [type : {"P1b"}, ballot : Ballots, acceptor : Replicas,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {none}]
  \cup [type : {"P2a"}, ballot : Ballots, value : Values \cup {any}]
  \cup [type : {"P2b"}, ballot : Ballots, acceptor : Replicas, value : Values]

Send(m) == messages' = messages \cup {m}

Proposed(v) == \E m \in messages : m.type = "propose" /\ m.value = v

-----------------------------------------------------------------------------

Init ==
  /\ messages = {}
  /\ decision = {}
  /\ maxBallot = [a \in Replicas |-> NoBallot]
  /\ maxVBallot = [a \in Replicas |-> NoBallot]
  /\ maxValue = [a \in Replicas |-> none]
  /\ cValue = none

Propose(v) ==
  /\ Send([type |-> "propose", value |-> v])
  /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue>>

Phase1a(b) ==
  /\ Send([type |-> "P1a", ballot |-> b])
  /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue>>

Phase1b(a) ==
  \E m \in messages :
    /\ m.type = "P1a"
    /\ m.ballot > maxBallot[a]
    /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
    /\ Send([type |-> "P1b", ballot |-> m.ballot, acceptor |-> a,
             mbal |-> maxVBallot[a], mval |-> maxValue[a]])
    /\ UNCHANGED <<decision, maxVBallot, maxValue, cValue>>

\* Coordinator phase 2a, with collision recovery for values accepted in fast rounds.
Phase2a(b) ==
  /\ ~\E m \in messages : m.type = "P2a" /\ m.ballot = b
  /\ \E Q \in Quorums :
       LET M == {m \in messages : /\ m.type = "P1b"
                                  /\ m.ballot = b
                                  /\ m.acceptor \in Q}
       IN /\ M # {}
          /\ \A a \in Q : \E m \in M : m.acceptor = a
          /\ LET k == Max({m.mbal : m \in M})
                 V == {m.mval : m \in {mm \in M : mm.mbal = k}}
                 O4(v) == \E R \in FastQuorums :
                            \A a \in R \cap Q :
                              \E m \in M : /\ m.acceptor = a
                                           /\ m.mbal = k
                                           /\ m.mval = v
             IN \E val \in Values \cup {any} :
                  /\ IF k = NoBallot
                       THEN IF b \in FastBallots
                              THEN val = any
                              ELSE val \in Values /\ Proposed(val)
                       ELSE IF k \in FastBallots
                              THEN IF \E v \in V : O4(v)
                                     THEN val \in V /\ O4(val)
                                     ELSE val \in V
                              ELSE val \in V
                  /\ Send([type |-> "P2a", ballot |-> b, value |-> val])
                  /\ cValue' = val
  /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>

\* The coordinator may start the very first ballot as a fast ballot
\* without executing phase 1.
FastAny(f) ==
  /\ f \in FastBallots
  /\ \A b \in Ballots : f <= b
  /\ ~\E m \in messages : m.type = "P2a" /\ m.ballot = f
  /\ Send([type |-> "P2a", ballot |-> f, value |-> any])
  /\ cValue' = any
  /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>

Phase2b(a) ==
  \E m \in messages :
    /\ m.type = "P2a"
    /\ m.value # any
    /\ m.ballot >= maxBallot[a]
    /\ maxVBallot[a] < m.ballot
    /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
    /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
    /\ maxValue' = [maxValue EXCEPT ![a] = m.value]
    /\ Send([type |-> "P2b", ballot |-> m.ballot, acceptor |-> a,
             value |-> m.value])
    /\ UNCHANGED <<decision, cValue>>

\* An acceptor in a fast round accepts a proposed value directly.
FastPropose(a, v) ==
  \E m \in messages :
    /\ m.type = "P2a"
    /\ m.value = any
    /\ m.ballot \in FastBallots
    /\ m.ballot >= maxBallot[a]
    /\ maxVBallot[a] < m.ballot
    /\ Proposed(v)
    /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
    /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
    /\ maxValue' = [maxValue EXCEPT ![a] = v]
    /\ Send([type |-> "P2b", ballot |-> m.ballot, acceptor |-> a, value |-> v])
    /\ UNCHANGED <<decision, cValue>>

Decide(b, v) ==
  /\ \E Q \in (IF b \in FastBallots THEN FastQuorums ELSE Quorums) :
       /\ Q # {}
       /\ \A a \in Q : \E m \in messages : /\ m.type = "P2b"
                                         /\ m.ballot = b
                                         /\ m.acceptor = a
                                         /\ m.value = v
  /\ decision' = decision \cup {v}
  /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>

FastNext ==
  \/ \E v \in Values : Propose(v)
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E a \in Replicas : Phase1b(a)
  \/ \E b \in Ballots : Phase2a(b)
  \/ \E f \in FastBallots : FastAny(f)
  \/ \E a \in Replicas : Phase2b(a)
  \/ \E a \in Replicas, v \in Values : FastPropose(a, v)
  \/ \E b \in Ballots, v \in Values : Decide(b, v)

FastSpec == Init /\ [][FastNext]_vars

-----------------------------------------------------------------------------

FastTypeOK ==
  /\ messages \subseteq Message
  /\ decision \subseteq Values
  /\ maxBallot \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxVBallot \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxValue \in [Replicas -> Values \cup {none}]
  /\ cValue \in Values \cup {any, none}

FastNontriviality ==
  \A v \in decision : \E m \in messages : m.type = "propose" /\ m.value = v

PaxosConsistency ==
  \A x, y \in decision : x = y

PaxosSymmetry == Permutations(Values)

=============================================================================
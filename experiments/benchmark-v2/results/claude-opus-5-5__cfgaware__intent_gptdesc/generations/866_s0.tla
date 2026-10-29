---- MODULE FastPaxos ----
EXTENDS Integers, FiniteSets, TLC

(***************************************************************************)
(* Fast Paxos for a single consensus instance.                             *)
(* Goal: at most one value is ever chosen, and only a proposed value can   *)
(* be chosen. Fast rounds let acceptors accept proposals directly once the *)
(* coordinator has sent "any". Classic rounds resolve collisions through   *)
(* the coordinator, which uses a prepare/accept (phase 1/phase 2) pattern  *)
(* and a safe value-selection rule.                                        *)
(***************************************************************************)

CONSTANTS any, none,
          r1, r2, r3, r4, Replicas,
          v1, v2, v3, Values,
          Ballots, FastBallots,
          Quorums, FastQuorums

ASSUME /\ any \notin Values
       /\ none \notin Values
       /\ any # none
       /\ Ballots \subseteq Nat
       /\ FastBallots \subseteq Ballots
       /\ \A Q \in Quorums : Q \subseteq Replicas
       /\ \A R \in FastQuorums : R \subseteq Replicas
       \* Any two classic quorums intersect.
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
       \* Any classic quorum and any two fast quorums have a common member.
       /\ \A Q \in Quorums : \A R1, R2 \in FastQuorums : Q \cap R1 \cap R2 # {}
       \* Any three fast quorums have a common member.
       /\ \A R1, R2, R3 \in FastQuorums : R1 \cap R2 \cap R3 # {}

ClassicBallots == Ballots \ FastBallots

NoBallot == -1

VARIABLES msgs,        \* set of all messages sent so far
          maxBallot,   \* highest ballot each acceptor has joined
          maxVBallot,  \* highest ballot in which each acceptor voted
          maxValue,    \* value voted for in maxVBallot
          cValue       \* the decided value (or none)

vars == <<msgs, maxBallot, maxVBallot, maxValue, cValue>>

Message ==
       [type : {"propose"}, value : Values]
  \cup [type : {"P1a"}, ballot : Ballots]
  \cup [type : {"P1b"}, ballot : Ballots, acceptor : Replicas,
        maxVBallot : Ballots \cup {NoBallot}, maxValue : Values \cup {none}]
  \cup [type : {"P2a"}, ballot : Ballots, value : Values \cup {any}]
  \cup [type : {"P2b"}, ballot : Ballots, acceptor : Replicas, value : Values]

Send(m) == msgs' = msgs \cup {m}

ProposedValues == {m.value : m \in {mm \in msgs : mm.type = "propose"}}

SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

(***************************************************************************)
(* Coordinator value-selection rule (conflict resolution).                 *)
(***************************************************************************)
P1bMsgs(b, Q) == {m \in msgs : m.type = "P1b" /\ m.ballot = b /\ m.acceptor \in Q}

HeardFrom(b, Q) == \A a \in Q : \E m \in P1bMsgs(b, Q) : m.acceptor = a

HighestVBallot(b, Q) == SetMax({m.maxVBallot : m \in P1bMsgs(b, Q)})

ReportedAtK(b, Q) ==
  LET k == HighestVBallot(b, Q)
  IN  {m.maxValue : m \in {mm \in P1bMsgs(b, Q) : mm.maxVBallot = k}}

\* w is held by every member of Q \cap R for some fast quorum R at ballot k,
\* i.e. w may have been chosen in fast round k.
MajorityInQuorum(b, Q, w) ==
  LET k == HighestVBallot(b, Q)
  IN  \E R \in FastQuorums :
        \A a \in Q \cap R :
          \E m \in P1bMsgs(b, Q) :
            /\ m.acceptor = a
            /\ m.maxVBallot = k
            /\ m.maxValue = w

SafeValue(b, Q, v) ==
  LET k == HighestVBallot(b, Q)
  IN  IF k = NoBallot
        THEN v \in ProposedValues
        ELSE IF k \in FastBallots /\ \E w \in Values : MajorityInQuorum(b, Q, w)
               THEN MajorityInQuorum(b, Q, v)
               ELSE v \in ReportedAtK(b, Q)

NoP2aYet(b) == ~ \E m \in msgs : m.type = "P2a" /\ m.ballot = b

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Init ==
  /\ msgs = {}
  /\ maxBallot = [a \in Replicas |-> NoBallot]
  /\ maxVBallot = [a \in Replicas |-> NoBallot]
  /\ maxValue = [a \in Replicas |-> none]
  /\ cValue = none

Propose(v) ==
  /\ Send([type |-> "propose", value |-> v])
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, cValue>>

Phase1a(b) ==
  /\ Send([type |-> "P1a", ballot |-> b])
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, cValue>>

Phase1b(a, b) ==
  /\ [type |-> "P1a", ballot |-> b] \in msgs
  /\ b > maxBallot[a]
  /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
  /\ Send([type |-> "P1b", ballot |-> b, acceptor |-> a,
           maxVBallot |-> maxVBallot[a], maxValue |-> maxValue[a]])
  /\ UNCHANGED <<maxVBallot, maxValue, cValue>>

\* Coordinator starts a fast round by sending "any" when nothing was voted.
FastAny(b) ==
  /\ b \in FastBallots
  /\ NoP2aYet(b)
  /\ \E Q \in Quorums :
        /\ HeardFrom(b, Q)
        /\ HighestVBallot(b, Q) = NoBallot
  /\ Send([type |-> "P2a", ballot |-> b, value |-> any])
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, cValue>>

\* Coordinator proposes a specific (safe) value; used for classic rounds
\* and for collision recovery.
Phase2a(b, v) ==
  /\ NoP2aYet(b)
  /\ \E Q \in Quorums :
        /\ HeardFrom(b, Q)
        /\ SafeValue(b, Q, v)
  /\ Send([type |-> "P2a", ballot |-> b, value |-> v])
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, cValue>>

ClassicPhase2b(a, b, v) ==
  /\ v \in Values
  /\ [type |-> "P2a", ballot |-> b, value |-> v] \in msgs
  /\ b >= maxBallot[a]
  /\ b > maxVBallot[a]
  /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
  /\ maxVBallot' = [maxVBallot EXCEPT ![a] = b]
  /\ maxValue' = [maxValue EXCEPT ![a] = v]
  /\ Send([type |-> "P2b", ballot |-> b, acceptor |-> a, value |-> v])
  /\ UNCHANGED cValue

\* Acceptor in a fast round accepts a proposal directly.
FastPhase2b(a, b, v) ==
  /\ b \in FastBallots
  /\ [type |-> "P2a", ballot |-> b, value |-> any] \in msgs
  /\ [type |-> "propose", value |-> v] \in msgs
  /\ b >= maxBallot[a]
  /\ b > maxVBallot[a]
  /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
  /\ maxVBallot' = [maxVBallot EXCEPT ![a] = b]
  /\ maxValue' = [maxValue EXCEPT ![a] = v]
  /\ Send([type |-> "P2b", ballot |-> b, acceptor |-> a, value |-> v])
  /\ UNCHANGED cValue

QuorumsOf(b) == IF b \in FastBallots THEN FastQuorums ELSE Quorums

Chosen(b, v) ==
  \E Q \in QuorumsOf(b) :
    \A a \in Q : [type |-> "P2b", ballot |-> b, acceptor |-> a, value |-> v] \in msgs

Decide(b, v) ==
  /\ Chosen(b, v)
  /\ cValue = none
  /\ cValue' = v
  /\ UNCHANGED <<msgs, maxBallot, maxVBallot, maxValue>>

DecideStep == \E b \in Ballots, v \in Values : Decide(b, v)

Next ==
  \/ \E v \in Values : Propose(v)
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E a \in Replicas, b \in Ballots : Phase1b(a, b)
  \/ \E b \in Ballots : FastAny(b)
  \/ \E b \in Ballots, v \in Values : Phase2a(b, v)
  \/ \E a \in Replicas, b \in Ballots, v \in Values : ClassicPhase2b(a, b, v)
  \/ \E a \in Replicas, b \in Ballots, v \in Values : FastPhase2b(a, b, v)
  \/ DecideStep

FastSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DecideStep)
  /\ \A a \in Replicas, b \in Ballots, v \in Values :
        /\ WF_vars(ClassicPhase2b(a, b, v))
        /\ WF_vars(Phase1b(a, b))

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
FastTypeOK ==
  /\ msgs \subseteq Message
  /\ maxBallot \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxVBallot \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxValue \in [Replicas -> Values \cup {none}]
  /\ cValue \in Values \cup {none}

FastNontriviality ==
  /\ cValue = none \/ cValue \in ProposedValues
  /\ \A m \in msgs : m.type = "P2b" => m.value \in ProposedValues

PaxosConsistency ==
  /\ \A b1, b2 \in Ballots, w1, w2 \in Values :
        (Chosen(b1, w1) /\ Chosen(b2, w2)) => w1 = w2
  /\ cValue # none => \A b \in Ballots, w \in Values : Chosen(b, w) => w = cValue

ValidConflictResolution ==
  \A m \in msgs :
    (m.type = "P2a" /\ m.value # any) =>
      \E Q \in Quorums : HeardFrom(m.ballot, Q) /\ SafeValue(m.ballot, Q, m.value)

PaxosSymmetry == Permutations(Values)

====
---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS any, none,
          r1, r2, r3, r4,
          v1, v2, v3,
          Replicas, Values, Ballots, Quorums

ASSUME /\ Ballots \subseteq Nat
       /\ none \notin Values
       /\ any \notin Values
       /\ \A Q \in Quorums : Q \subseteq Replicas
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

NoBallot == -1

VARIABLES maxBal,    \* highest ballot promised by each acceptor
          maxVBal,   \* highest ballot in which each acceptor accepted
          maxVal,    \* value accepted in maxVBal
          msgs,      \* set of all messages ever sent (unordered, may be re-delivered)
          proposed,  \* values proposed by proposers
          decided    \* values decided

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, decided>>

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Replicas, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {none}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Replicas, bal : Ballots, val : Values]

PaxosTypeOK ==
  /\ maxBal   \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxVBal  \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxVal   \in [Replicas -> Values \cup {none}]
  /\ msgs     \subseteq Message
  /\ proposed \subseteq Values
  /\ decided  \subseteq Values

QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

PaxosInit ==
  /\ maxBal   = [a \in Replicas |-> NoBallot]
  /\ maxVBal  = [a \in Replicas |-> NoBallot]
  /\ maxVal   = [a \in Replicas |-> none]
  /\ msgs     = {}
  /\ proposed = {}
  /\ decided  = {}

Send(m) == msgs' = msgs \cup {m}

\* A proposer (client) proposes a value
Propose(v) ==
  /\ v \notin proposed
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, decided>>

\* Proposer starts ballot b by sending Prepare
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

\* Acceptor promises
Phase1b(a) ==
  /\ \E m \in msgs :
       /\ m.type = "1a"
       /\ m.bal > maxBal[a]
       /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal, proposed, decided>>

\* Proposer sends Accept request after promises from a quorum
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
           Q1bv == {m \in Q1b : m.mbal # NoBallot}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ /\ Q1bv = {}
                 /\ v \in proposed
              \/ \E m \in Q1bv :
                   /\ m.mval = v
                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

\* Acceptor accepts if no promise is violated
Phase2b(a) ==
  /\ \E m \in msgs :
       /\ m.type = "2a"
       /\ m.bal >= maxBal[a]
       /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
       /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
       /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
       /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
  /\ UNCHANGED <<proposed, decided>>

\* Decision derived from a quorum of matching Accepted messages
Decide(b, v) ==
  /\ \E Q \in Quorums :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v
  /\ decided' = decided \cup {v}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposed>>

PaxosNext ==
  \/ \E v \in Values : Propose(v)
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E b \in Ballots, v \in Values : Phase2a(b, v)
  \/ \E a \in Replicas : Phase1b(a) \/ Phase2b(a)
  \/ \E b \in Ballots, v \in Values : Decide(b, v)

PaxosSpec == PaxosInit /\ [][PaxosNext]_vars

\* Safety properties
PaxosConsistency == \A v, w \in decided : v = w

PaxosNontriviality == decided \subseteq proposed

Chosen(v) == \E b \in Ballots, Q \in Quorums :
               \A a \in Q : \E m \in msgs :
                  m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

ChosenConsistency == \A v, w \in Values : Chosen(v) /\ Chosen(w) => v = w

AcceptorInv == \A a \in Replicas :
                 /\ maxVBal[a] <= maxBal[a]
                 /\ (maxVBal[a] = NoBallot) <=> (maxVal[a] = none)

PaxosMonotonicity ==
  [][\A a \in Replicas :
       /\ maxBal'[a] >= maxBal[a]
       /\ maxVBal'[a] >= maxVBal[a]
       /\ (maxVBal'[a] = maxVBal[a]) => (maxVal'[a] = maxVal[a])]_vars

PaxosSymmetry == Permutations(Replicas) \cup Permutations(Values)

=============================================================================
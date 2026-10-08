----------------------------- MODULE Paxos -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Replicas,       \* nonempty finite set of nodes; each acts as proposer and acceptor
  Values,         \* nonempty set of possible values
  Ballots,        \* set of ballot numbers, including 0 as sentinel; totally ordered by Naturals
  Quorums,        \* collection of majority quorums; pairwise intersecting
  Owner,          \* function mapping each ballot to its unique owner (proposer)
  None            \* distinguished token not in Values

ASSUME
  /\ None \notin Values
  /\ Ballots \subseteq Nat
  /\ 0 \in Ballots
  /\ \A Q \in Quorums:
        Q \subseteq Replicas
        /\ Q # {}
        /\ Cardinality(Q) > Cardinality(Replicas) \div 2
  /\ \A Q1 \in Quorums: \A Q2 \in Quorums: Q1 \cap Q2 # {}
  /\ Owner \in [Ballots -> Replicas]
  /\ \A b \in Ballots \ {0}: Owner[b] \in Replicas

VARIABLES
  promised,       \* [r \in Replicas -> Ballots], highest ballot promised (i.e., seen) by r
  acceptedBal,    \* [r \in Replicas -> Ballots], highest ballot accepted by r (0 if none)
  acceptedVal,    \* [r \in Replicas -> Values \cup {None}], value accepted by r (None if none)
  Msgs,           \* set of in-flight messages (records)
  Proposed,       \* set of values that have been proposed via Accept requests
  Decisions       \* set of decided pairs [b: Ballots, v: Values]

vars == << promised, acceptedBal, acceptedVal, Msgs, Proposed, Decisions >>

\* Message record schemas (informal, for reference):
\* Prepare: [type |-> "Prepare", from |-> p, to |-> a, bal |-> b]
\* Promise: [type |-> "Promise", from |-> a, to |-> p, bal |-> b, prevBal |-> ab, prevVal |-> av]
\* Accept:  [type |-> "Accept",  from |-> p, to |-> a, bal |-> b, val |-> v]
\* Accepted:[type |-> "Accepted",from |-> a,              bal |-> b, val |-> v]

TypeOK ==
  /\ promised \in [Replicas -> Ballots]
  /\ acceptedBal \in [Replicas -> Ballots]
  /\ acceptedVal \in [Replicas -> Values \cup {None}]
  /\ Msgs \subseteq
       UNION {
         { [type |-> "Prepare", from |-> p, to |-> a, bal |-> b] :
              p \in Replicas, a \in Replicas, b \in Ballots \ {0} },
         { [type |-> "Promise", from |-> a, to |-> p, bal |-> b, prevBal |-> ab, prevVal |-> av] :
              a \in Replicas, p \in Replicas, b \in Ballots \ {0},
              ab \in Ballots, av \in Values \cup {None} },
         { [type |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> v] :
              p \in Replicas, a \in Replicas, b \in Ballots \ {0}, v \in Values },
         { [type |-> "Accepted", from |-> a, bal |-> b, val |-> v] :
              a \in Replicas, b \in Ballots \ {0}, v \in Values }
       }
  /\ Proposed \subseteq Values
  /\ Decisions \subseteq { [b |-> b, v |-> v] : b \in Ballots \ {0}, v \in Values }

Init ==
  /\ TypeOK
  /\ \A r \in Replicas:
        /\ promised[r] = 0
        /\ acceptedBal[r] = 0
        /\ acceptedVal[r] = None
  /\ Msgs = {}
  /\ Proposed = {}
  /\ Decisions = {}

Max(S) ==
  CHOOSE m \in S : \A n \in S : m >= n

SendPrepare ==
  \E b \in Ballots \ {0}:
    LET p == Owner[b] IN
      \E a \in Replicas:
        /\ Msgs' = Msgs \cup { [type |-> "Prepare", from |-> p, to |-> a, bal |-> b] }
        /\ UNCHANGED << promised, acceptedBal, acceptedVal, Proposed, Decisions >>

RecvPrepare ==
  \E m \in Msgs:
    /\ m.type = "Prepare"
    /\ LET a == m.to IN
       LET b == m.bal IN
         /\ b >= promised[a]
         /\ promised' = [promised EXCEPT ![a] = b]
         /\ Msgs' = (Msgs \ {m})
                    \cup { [ type |-> "Promise",
                             from |-> a, to |-> m.from, bal |-> b,
                             prevBal |-> acceptedBal[a], prevVal |-> acceptedVal[a] ] }
         /\ UNCHANGED << acceptedBal, acceptedVal, Proposed, Decisions >>

SendAccept ==
  \E b \in Ballots \ {0}:
    LET p == Owner[b] IN
      \E Q \in Quorums:
        LET S == { m \in Msgs :
                     m.type = "Promise" /\ m.to = p /\ m.bal = b } IN
        /\ Q \subseteq { m.from : m \in S }
        /\ LET H == { m \in S : m.from \in Q /\ m.prevVal # None /\ m.prevBal \in Ballots } IN
           LET v == IF H = {}
                    THEN CHOOSE vv \in Values : TRUE
                    ELSE LET k == Max({ m.prevBal : m \in H }) IN
                         CHOOSE vv \in { m.prevVal : m \in H /\ m.prevBal = k } : TRUE
           IN
             /\ Msgs' = Msgs \cup { [type |-> "Accept", from |-> p, to |-> CHOOSE a \in Replicas : TRUE,
                                      bal |-> b, val |-> v] }
             /\ Proposed' = Proposed \cup { v }
             /\ UNCHANGED << promised, acceptedBal, acceptedVal, Decisions >>

RecvAccept ==
  \E m \in Msgs:
    /\ m.type = "Accept"
    /\ LET a == m.to IN
       LET b == m.bal IN
       LET v == m.val IN
         /\ b >= promised[a]
         /\ promised' = [promised EXCEPT ![a] = b]
         /\ acceptedBal' = [acceptedBal EXCEPT ![a] = b]
         /\ acceptedVal' = [acceptedVal EXCEPT ![a] = v]
         /\ Msgs' = (Msgs \ {m})
                    \cup { [type |-> "Accepted", from |-> a, bal |-> b, val |-> v] }
         /\ UNCHANGED << Proposed, Decisions >>

Decide ==
  \E b \in Ballots \ {0}:
    \E v \in Values:
      \E Q \in Quorums:
        /\ \A a \in Q:
             \E m \in Msgs:
               m.type = "Accepted" /\ m.from = a /\ m.bal = b /\ m.val = v
        /\ Decisions' = Decisions \cup { [b |-> b, v |-> v] }
        /\ UNCHANGED << promised, acceptedBal, acceptedVal, Msgs, Proposed >>

Next ==
  SendPrepare
  \/ RecvPrepare
  \/ SendAccept
  \/ RecvAccept
  \/ Decide

\* Safety properties
NonTriviality ==
  \A d \in Decisions : d.v \in Proposed

Consistency ==
  \A d1 \in Decisions : \A d2 \in Decisions : d1.v = d2.v

Spec ==
  Init /\ [][Next]_vars /\ SF_vars(Decide)

============================================================================
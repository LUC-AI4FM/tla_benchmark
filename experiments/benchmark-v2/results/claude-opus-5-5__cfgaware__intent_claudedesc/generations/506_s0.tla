---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME QuorumAssumption ==
          /\ \A Q \in Quorums : Q \subseteq Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

ConstBallots == 0..2

SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

(* "No value" is represented by the empty set; a value v by {v}. *)
OptValues == {{}} \cup {{v} : v \in Values}

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : OptValues]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal, maxVBal, maxVal, msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
  /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal  \in [Acceptors -> OptValues]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal  = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal  = [a \in Acceptors |-> {}]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
              mbal |-> maxVBal[a], mval |-> maxVal[a]])
     /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                    /\ v \in m.mval
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[a]
     /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![a] = {m.val}]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
  \/ \E b \in Ballots : \/ Phase1a(b)
                        \/ \E v \in Values : Phase2a(b, v)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
VotedForIn(a, v, b) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.acc = a
                  /\ m.val = v
                  /\ m.bal = b

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

chosen == {v \in Values : \E b \in Ballots : ChosenIn(v, b)}

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ maxBal[a] > b

SafeAt(v, b) ==
  \A c \in {d \in Ballots : d < b} :
     \E Q \in Quorums :
        \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)

MessageInv ==
  \A m \in msgs :
     /\ (m.type = "1b") =>
           /\ m.bal =< maxBal[m.acc]
           /\ \/ /\ m.mbal = -1
                 /\ m.mval = {}
              \/ /\ m.mbal \in Ballots
                 /\ \E v \in m.mval : VotedForIn(m.acc, v, m.mbal)
           /\ \A c \in Ballots :
                 (c > m.mbal /\ c < m.bal) =>
                    ~ \E v \in Values : VotedForIn(m.acc, v, c)
     /\ (m.type = "2a") =>
           /\ SafeAt(m.val, m.bal)
           /\ \A ma \in msgs : (ma.type = "2a" /\ ma.bal = m.bal) => ma = m
     /\ (m.type = "2b") =>
           /\ \E ma \in msgs : /\ ma.type = "2a"
                               /\ ma.bal = m.bal
                               /\ ma.val = m.val
           /\ m.bal =< maxVBal[m.acc]

AcceptorInv ==
  \A a \in Acceptors :
     /\ (maxVal[a] = {}) <=> (maxVBal[a] = -1)
     /\ maxVBal[a] =< maxBal[a]
     /\ (maxVBal[a] >= 0) => \E v \in maxVal[a] : VotedForIn(a, v, maxVBal[a])
     /\ \A c \in Ballots :
           c > maxVBal[a] => ~ \E v \in Values : VotedForIn(a, v, c)

ConsistencyInv == \A v1, v2 \in chosen : v1 = v2

-----------------------------------------------------------------------------
(* Abstract consensus specification, applied to the set chosen. *)
ConsensusInit == chosen = {}

ConsensusNext == /\ chosen = {}
                 /\ \E v \in Values : chosen' = {v}

ConsensusSpec == ConsensusInit /\ [][ConsensusNext]_chosen

=============================================================================
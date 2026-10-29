---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Values, Quorums

Ballots == Nat

ConstBallots == 0..2

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal, maxVBal, maxVal, msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK == /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVal  \in [Acceptors -> Values \cup {None}]
          /\ msgs \subseteq Messages

Init == /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]
        /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

(* A proposer initiates a new ballot b *)
Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(* An acceptor promises not to participate in lower ballots *)
Phase1b(a) ==
  /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal>>

(* A proposer picks a value consistent with responses from a quorum *)
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(* An acceptor accepts a proposal consistent with its promise *)
Phase2b(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[a]
     /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next == \/ \E b \in Ballots : Phase1a(b) \/ \E v \in Values : Phase2a(b, v)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
MsgBallots == {m.bal : m \in msgs}

VotedFor(a, b, v) ==
  [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Values : \E b \in MsgBallots : ChosenAt(b, v)}

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedFor(a, b, v)
                    /\ maxBal[a] > b

SafeAt(v, b) ==
  \A c \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedFor(a, c, v) \/ WontVoteIn(a, c)

MessageInv ==
  \A m \in msgs :
    /\ (m.type = "1b") =>
          /\ m.bal =< maxBal[m.acc]
          /\ \/ /\ m.mval \in Values
                /\ m.mbal \in Ballots
                /\ VotedFor(m.acc, m.mbal, m.mval)
             \/ /\ m.mval = None
                /\ m.mbal = -1
          /\ \A c \in (m.mbal + 1)..(m.bal - 1) :
                \A v \in Values : ~ VotedFor(m.acc, c, v)
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
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]
    /\ (maxVBal[a] >= 0) => VotedFor(a, maxVBal[a], maxVal[a])
    /\ \A c \in MsgBallots :
          c > maxVBal[a] => \A v \in Values : ~ VotedFor(a, c, v)
    /\ \A m1, m2 \in msgs :
          (/\ m1.type = "2b" /\ m2.type = "2b"
           /\ m1.acc = a /\ m2.acc = a
           /\ m1.bal = m2.bal) => m1.val = m2.val

ConsistencyInv == \A v1, v2 \in chosen : v1 = v2

-----------------------------------------------------------------------------
(* The high-level consensus specification refined by Paxos *)
ConsensusInit == chosen = {}

ConsensusNext == /\ chosen = {}
                 /\ \E v \in Values : chosen' = {v}

ConsensusSpec == ConsensusInit /\ [][ConsensusNext]_chosen

(* Optional liveness notion *)
Liveness == <>(chosen # {})

=============================================================================
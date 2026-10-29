------------------------------- MODULE MCPaxos -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Quorums, Values, Ballots

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

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

Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
  /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
        LET S == {m \in msgs : /\ m.type = "1b"
                               /\ m.acc \in Q
                               /\ m.bal = b}
        IN  /\ \A a \in Q : \E m \in S : m.acc = a
            /\ \/ \A m \in S : m.mbal = -1
               \/ \E c \in 0..(b-1) :
                     /\ \A m \in S : m.mbal =< c
                     /\ \E m \in S : /\ m.mbal = c
                                     /\ m.mval = v
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[a]
     /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next == \/ \E b \in Ballots : \/ Phase1a(b)
                              \/ \E v \in Values : Phase2a(b, v)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper definitions *)

VotedFor(a, b, v) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.acc = a
                  /\ m.bal = b
                  /\ m.val = v

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Values : \E b \in Ballots : ChosenAt(b, v)}

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedFor(a, b, v)
                    /\ maxBal[a] > b

SafeAt(b, v) ==
  \A c \in {d \in Ballots : d < b} :
     \E Q \in Quorums :
        \A a \in Q : VotedFor(a, c, v) \/ WontVoteIn(a, c)

-----------------------------------------------------------------------------
(* Invariants *)

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
                ~ \E v \in Values : VotedFor(m.acc, c, v)
    /\ (m.type = "2a") =>
          /\ SafeAt(m.bal, m.val)
          /\ \A ma \in msgs : (ma.type = "2a" /\ ma.bal = m.bal) => (ma = m)
    /\ (m.type = "2b") =>
          /\ \E ma \in msgs : /\ ma.type = "2a"
                              /\ ma.bal = m.bal
                              /\ ma.val = m.val
          /\ m.bal =< maxBal[m.acc]

AcceptorInv ==
  \A a \in Acceptors :
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]
    /\ (maxVBal[a] >= 0) => VotedFor(a, maxVBal[a], maxVal[a])
    /\ \A c \in Ballots :
          c > maxVBal[a] => ~ \E v \in Values : VotedFor(a, c, v)

ConsistencyInv == \A v, w \in chosen : v = w

-----------------------------------------------------------------------------
(* Model-checking helpers *)

ConstBallots == 0..2

SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

-----------------------------------------------------------------------------
(* Refinement of the single-value Consensus specification, with its        *)
(* variable chosen mapped to the set of values chosen by Paxos.            *)

ConsensusInit == chosen = {}

ConsensusNext == /\ chosen = {}
                 /\ \E v \in Values : chosen' = {v}

ConsensusSpec == ConsensusInit /\ [][ConsensusNext]_chosen

=============================================================================
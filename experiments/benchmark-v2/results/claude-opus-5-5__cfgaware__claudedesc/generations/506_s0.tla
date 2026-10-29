---- MODULE MCPaxosPlusCal ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Values, Quorums, Ballots

ConstBallots == 0..2

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorums : Q \subseteq Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == "None"

Message ==
         [type : {"1a"}, bal : Ballots]
    \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
          mbal : Ballots \cup {-1}, mval : Values \cup {None}]
    \cup [type : {"2a"}, bal : Ballots, val : Values]
    \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES msgs, maxPrepared, maxAccepted, maxVal

vars == << msgs, maxPrepared, maxAccepted, maxVal >>

Send(m) == msgs' = msgs \cup {m}

Init ==
    /\ msgs = {}
    /\ maxPrepared = [a \in Acceptors |-> -1]
    /\ maxAccepted = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]

Phase1a(b) ==
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED << maxPrepared, maxAccepted, maxVal >>

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxPrepared[a]
        /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxAccepted[a], mval |-> maxVal[a]])
        /\ UNCHANGED << maxAccepted, maxVal >>

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
    /\ UNCHANGED << maxPrepared, maxAccepted, maxVal >>

Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxPrepared[a]
        /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
        /\ maxAccepted' = [maxAccepted EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
    \/ \E b \in Ballots : Phase1a(b) \/ \E v \in Values : Phase2a(b, v)
    \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

VotedFor(a, b, v) == [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

CannotVoteAt(a, b) ==
    /\ maxPrepared[a] > b
    /\ \A v \in Values : ~ VotedFor(a, b, v)

ChosenIn(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenIn(b, v)

SafeAt(b, v) ==
    \A c \in Ballots :
        c < b => \E Q \in Quorums :
                    \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)

TypeOK ==
    /\ msgs \subseteq Message
    /\ maxPrepared \in [Acceptors -> Ballots \cup {-1}]
    /\ maxAccepted \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]

MessageInv ==
    \A m \in msgs :
        /\ (m.type = "1b") =>
              /\ m.bal <= maxPrepared[m.acc]
              /\ m.mbal < m.bal
              /\ (m.mbal >= 0) => VotedFor(m.acc, m.mbal, m.mval)
              /\ \A c \in Ballots :
                    (m.mbal < c /\ c < m.bal) =>
                        \A v \in Values : ~ VotedFor(m.acc, c, v)
        /\ (m.type = "2a") =>
              /\ SafeAt(m.bal, m.val)
              /\ \A m2 \in msgs :
                    (m2.type = "2a" /\ m2.bal = m.bal) => m2.val = m.val
        /\ (m.type = "2b") =>
              /\ \E m2 \in msgs :
                    /\ m2.type = "2a"
                    /\ m2.bal = m.bal
                    /\ m2.val = m.val
              /\ m.bal <= maxAccepted[m.acc]

AcceptorInv ==
    \A a \in Acceptors :
        /\ maxAccepted[a] <= maxPrepared[a]
        /\ (maxAccepted[a] = -1) <=> (maxVal[a] = None)
        /\ (maxAccepted[a] >= 0) => VotedFor(a, maxAccepted[a], maxVal[a])
        /\ \A c \in Ballots :
              c > maxAccepted[a] => \A v \in Values : ~ VotedFor(a, c, v)

ConsistencyInv == \A v, w \in Values : Chosen(v) /\ Chosen(w) => v = w

-----------------------------------------------------------------------------

chosenSet == {v \in Values : Chosen(v)}

CInit == chosenSet = {}

CNext == /\ chosenSet = {}
         /\ \E v \in Values : chosenSet' = {v}

ConsensusSpec == CInit /\ [][CNext]_chosenSet

SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

=============================================================================
---- MODULE Paxos ----
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal, maxVBal, maxVal, msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
    /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal  \in [Acceptors -> Values \cup {None}]
    /\ msgs \subseteq Message

Init ==
    /\ maxBal  = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal  = [a \in Acceptors |-> None]
    /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

\* Phase 1a: leader initiates a ballot (only once per ballot)
Phase1a(b) ==
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Phase 1b: acceptor promises
Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
        /\ UNCHANGED <<maxVBal, maxVal>>

\* Phase 2a: leader proposes a value after a quorum of promises
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

\* Phase 2b: acceptor votes
Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
    \/ \E b \in Ballots : Phase1a(b) \/ \E v \in Values : Phase2a(b, v)
    \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

VotedForIn(a, v, b) ==
    \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.val = v /\ m.bal = b

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)

Validity ==
    \A v \in Values : Chosen(v) =>
        \E m \in msgs : m.type = "2a" /\ m.val = v

=============================================================================
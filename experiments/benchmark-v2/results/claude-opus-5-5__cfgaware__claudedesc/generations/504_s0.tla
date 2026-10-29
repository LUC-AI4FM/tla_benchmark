---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Quorums, Values, Ballots

ASSUME /\ IsFiniteSet(Acceptors)
       /\ Cardinality(Acceptors) >= 3
       /\ Quorums \subseteq SUBSET Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
       /\ IsFiniteSet(Values)
       /\ Cardinality(Values) >= 2
       /\ 0 \notin Values
       /\ IsFiniteSet(Ballots)
       /\ Ballots \subseteq Nat

VARIABLES msgs, maxPrepared, maxAccepted, valAccepted

vars == <<msgs, maxPrepared, maxAccepted, valAccepted>>

None == 0

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxPrepared \in [Acceptors -> Ballots \cup {-1}]
  /\ maxAccepted \in [Acceptors -> Ballots \cup {-1}]
  /\ valAccepted \in [Acceptors -> Values \cup {None}]

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ msgs = {}
  /\ maxPrepared = [a \in Acceptors |-> -1]
  /\ maxAccepted = [a \in Acceptors |-> -1]
  /\ valAccepted = [a \in Acceptors |-> None]

Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxPrepared[a]
    /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxAccepted[a], mval |-> valAccepted[a]])
    /\ UNCHANGED <<maxAccepted, valAccepted>>

Phase2a(b) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums, v \in Values :
       LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                   /\ m.mval = v
                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
           /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxPrepared[a]
    /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
    /\ maxAccepted' = [maxAccepted EXCEPT ![a] = m.bal]
    /\ valAccepted' = [valAccepted EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
  \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
=============================================================================
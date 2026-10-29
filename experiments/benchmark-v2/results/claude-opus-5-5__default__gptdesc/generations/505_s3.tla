---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptor, Value, Quorum

ASSUME QuorumAssumption ==
          /\ IsFiniteSet(Acceptor)
          /\ IsFiniteSet(Value)
          /\ Quorum \subseteq SUBSET Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

None == CHOOSE v : v \notin Value

Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

(***************************************************************************
--algorithm Paxos {
  variables maxBal  = [a \in Acceptor |-> -1],
            maxVBal = [a \in Acceptor |-> -1],
            maxVal  = [a \in Acceptor |-> None],
            msgs    = {};
  define { Send(m) == msgs \cup {m} }
  macro Phase1a(b) { ... }  macro Phase1b(a) { ... }
  macro Phase2a(b) { ... }  macro Phase2b(a) { ... }
  process (Leader \in Ballot) { lbl: while (TRUE) { either Phase1a(self) or Phase2a(self) } }
  process (Acc \in Acceptor) { acc: while (TRUE) { either Phase1b(self) or Phase2b(self) } }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVal, msgs

vars == << maxBal, maxVBal, maxVal, msgs >>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
  /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVal  \in [Acceptor -> Value \cup {None}]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal  = [a \in Acceptor |-> -1]
  /\ maxVBal = [a \in Acceptor |-> -1]
  /\ maxVal  = [a \in Acceptor |-> None]
  /\ msgs    = {}

Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
              mbal |-> maxVBal[a], mval |-> maxVal[a]])
     /\ UNCHANGED << maxVBal, maxVal >>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum :
        LET Q1b  == {m \in msgs : /\ m.type = "1b"
                                  /\ m.acc \in Q
                                  /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal >= 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                     /\ m.mval = v
                     /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Phase2b(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[a]
     /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Leader(self) == \/ Phase1a(self)
                \/ \E v \in Value : Phase2a(self, v)

Acc(self) == \/ Phase1b(self)
             \/ Phase2b(self)

Next == \/ \E self \in Ballot : Leader(self)
        \/ \E self \in Acceptor : Acc(self)

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.acc = a
                                       /\ m.bal = b
                                       /\ m.val = v

ChosenIn(v, b) == \E Q \in Quorum : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballot : ChosenIn(v, b)

Consistency == \A v1, v2 \in Value : Chosen(v1) /\ Chosen(v2) => (v1 = v2)

THEOREM Spec => [](TypeOK /\ Consistency)
=============================================================================
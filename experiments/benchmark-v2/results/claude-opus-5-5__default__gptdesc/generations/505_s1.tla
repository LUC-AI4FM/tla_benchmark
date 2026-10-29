------------------------------- MODULE PaxosFixedLeader -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptor, Value, Quorum

ASSUME QuorumAssumption ==
          /\ IsFiniteSet(Acceptor)
          /\ IsFiniteSet(Value)
          /\ Quorum \subseteq SUBSET Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

ASSUME BallotAssumption == Ballot \cap Acceptor = {}

None == CHOOSE v : v \notin Value

Message ==
       [type : {"1a"}, bal : Ballot]
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
  define {
    sentMsgs(t, b) == {m \in msgs : m.type = t /\ m.bal = b}
  }
  macro Send(m) { msgs := msgs \cup {m} }

  process (Leader \in Ballot) {
    L1: Send([type |-> "1a", bal |-> self]);
    L2: with (Q \in Quorum,
              S = {m \in sentMsgs("1b", self) : m.acc \in Q}) {
          await \A a \in Q : \E m \in S : m.acc = a;
          with (w \in {m \in S : \A mm \in S : m.mbal >= mm.mbal}) {
            if (w.mbal = -1) {
              with (v \in Value) Send([type |-> "2a", bal |-> self, val |-> v])
            } else Send([type |-> "2a", bal |-> self, val |-> w.mval])
          }
        }
  }

  process (Acc \in Acceptor) {
    A: while (TRUE) {
         either with (m \in {mm \in msgs : mm.type = "1a" /\ mm.bal > maxBal[self]}) {
                  maxBal[self] := m.bal;
                  Send([type |-> "1b", acc |-> self, bal |-> m.bal,
                        mbal |-> maxVBal[self], mval |-> maxVal[self]])
                }
         or     with (m \in {mm \in msgs : mm.type = "2a" /\ mm.bal >= maxBal[self]}) {
                  maxBal[self] := m.bal;
                  maxVBal[self] := m.bal;
                  maxVal[self] := m.val;
                  Send([type |-> "2b", acc |-> self, bal |-> m.bal, val |-> m.val])
                }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVal, msgs, pc

sentMsgs(t, b) == {m \in msgs : m.type = t /\ m.bal = b}

vars == << maxBal, maxVBal, maxVal, msgs, pc >>

ProcSet == (Ballot) \cup (Acceptor)

Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVal  = [a \in Acceptor |-> None]
        /\ msgs = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Ballot   -> "L1"
                                        [] self \in Acceptor -> "A"]

L1(self) == /\ pc[self] = "L1"
            /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << maxBal, maxVBal, maxVal >>

L2(self) == /\ pc[self] = "L2"
            /\ \E Q \in Quorum :
                 LET S == {m \in sentMsgs("1b", self) : m.acc \in Q} IN
                   /\ \A a \in Q : \E m \in S : m.acc = a
                   /\ \E w \in {m \in S : \A mm \in S : m.mbal >= mm.mbal} :
                        IF w.mbal = -1
                          THEN \E v \in Value :
                                 msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
                          ELSE msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> w.mval]})
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Leader(self) == L1(self) \/ L2(self)

A(self) == /\ pc[self] = "A"
           /\ \/ /\ \E m \in {mm \in msgs : mm.type = "1a" /\ mm.bal > maxBal[self]} :
                      /\ maxBal' = [maxBal EXCEPT ![self] = m.bal]
                      /\ msgs' = (msgs \cup {[type |-> "1b", acc |-> self, bal |-> m.bal,
                                              mbal |-> maxVBal[self], mval |-> maxVal[self]]})
                 /\ UNCHANGED << maxVBal, maxVal >>
              \/ /\ \E m \in {mm \in msgs : mm.type = "2a" /\ mm.bal >= maxBal[self]} :
                      /\ maxBal' = [maxBal EXCEPT ![self] = m.bal]
                      /\ maxVBal' = [maxVBal EXCEPT ![self] = m.bal]
                      /\ maxVal' = [maxVal EXCEPT ![self] = m.val]
                      /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self,
                                              bal |-> m.bal, val |-> m.val]})
           /\ pc' = [pc EXCEPT ![self] = "A"]

Acc(self) == A(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ (\E self \in Ballot : Leader(self))
        \/ (\E self \in Acceptor : Acc(self))
        \/ Terminating

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal  \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message
          /\ pc \in [ProcSet -> {"L1", "L2", "A", "Done"}]

VotedFor(a, b, v) == [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Consistency == Cardinality(chosen) <= 1

=============================================================================
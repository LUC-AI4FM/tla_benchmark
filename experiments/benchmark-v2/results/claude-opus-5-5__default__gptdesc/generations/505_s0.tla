---- MODULE PaxosFixedLeader ----
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption ==
          /\ IsFiniteSet(Acceptors)
          /\ IsFiniteSet(Values)
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME DisjointIds == Acceptors \cap Nat = {}

Ballots == Nat

None == CHOOSE v : v \notin Values

(* Each ballot b has a fixed leader, the proposer process with id b. *)
Proposers == Ballots

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES msgs, maxBal, maxVBal, maxVal, pc

vars == << msgs, maxBal, maxVBal, maxVal, pc >>

ProcSet == Proposers \cup Acceptors

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ msgs = {}
  /\ maxBal = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal = [a \in Acceptors |-> None]
  /\ pc = [self \in ProcSet |-> IF self \in Proposers THEN "P1" ELSE "A"]

(* Proposer (leader of ballot self) *)
P1(self) ==
  /\ pc[self] = "P1"
  /\ Send([type |-> "1a", bal |-> self])
  /\ pc' = [pc EXCEPT ![self] = "P2"]
  /\ UNCHANGED << maxBal, maxVBal, maxVal >>

P2(self) ==
  /\ pc[self] = "P2"
  /\ \E Q \in Quorums :
       LET S == {m \in msgs : /\ m.type = "1b"
                              /\ m.bal = self
                              /\ m.acc \in Q}
       IN  /\ \A a \in Q : \E m \in S : m.acc = a
           /\ \E v \in Values :
                /\ \/ \A m \in S : m.mbal = -1
                   \/ \E m \in S : /\ m.mbal >= 0
                                   /\ m.mval = v
                                   /\ \A mm \in S : mm.mbal <= m.mbal
                /\ Send([type |-> "2a", bal |-> self, val |-> v])
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Proposer(self) == P1(self) \/ P2(self)

(* Acceptor *)
A(self) ==
  /\ pc[self] = "A"
  /\ \/ \E m \in msgs :
          /\ m.type = "1a"
          /\ m.bal > maxBal[self]
          /\ maxBal' = [maxBal EXCEPT ![self] = m.bal]
          /\ Send([type |-> "1b", acc |-> self, bal |-> m.bal,
                   mbal |-> maxVBal[self], mval |-> maxVal[self]])
          /\ UNCHANGED << maxVBal, maxVal >>
     \/ \E m \in msgs :
          /\ m.type = "2a"
          /\ m.bal >= maxBal[self]
          /\ maxBal' = [maxBal EXCEPT ![self] = m.bal]
          /\ maxVBal' = [maxVBal EXCEPT ![self] = m.bal]
          /\ maxVal' = [maxVal EXCEPT ![self] = m.val]
          /\ Send([type |-> "2b", acc |-> self, bal |-> m.bal, val |-> m.val])
  /\ pc' = [pc EXCEPT ![self] = "A"]

Acceptor(self) == A(self)

Next == \/ \E self \in Proposers : Proposer(self)
        \/ \E self \in Acceptors : Acceptor(self)

Spec == Init /\ [][Next]_vars

(* Safety properties *)
TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal \in [Acceptors -> Values \cup {None}]
  /\ pc \in [ProcSet -> {"P1", "P2", "Done", "A"}]

VotedFor(a, b, v) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.acc = a
                  /\ m.bal = b
                  /\ m.val = v

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E m \in msgs : m.type = "2b" /\ ChosenAt(m.bal, v)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

OneValuePerBallot ==
  \A m1, m2 \in msgs :
     (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1.val = m2.val

THEOREM Spec => [](TypeOK /\ Consistency)
====
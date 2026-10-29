---------------------------- MODULE FixedLeaderPaxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME /\ IsFiniteSet(Acceptors)
       /\ IsFiniteSet(Values)
       /\ Ballots \subseteq Nat
       /\ Acceptors \cap Ballots = {}
       /\ Quorums \subseteq SUBSET Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

(***************************************************************************
--algorithm FixedLeaderPaxos {
  variables msgs = {},
            maxBal  = [a \in Acceptors |-> -1],
            maxVBal = [a \in Acceptors |-> -1],
            maxVal  = [a \in Acceptors |-> None];

  process (Proposer \in Ballots) {
    P1a: msgs := msgs \cup {[type |-> "1a", bal |-> self]};
    P2a: with (Q \in Quorums) { ... send 2a for safe value ... }
  }

  process (Acceptor \in Acceptors) {
    A: while (TRUE) {
         with (m \in msgs) { ... handle 1a or 2a ... }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES msgs, maxBal, maxVBal, maxVal, pc

vars == << msgs, maxBal, maxVBal, maxVal, pc >>

ProcSet == Ballots \cup Acceptors

Init == /\ msgs = {}
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]
        /\ pc = [self \in ProcSet |-> CASE self \in Ballots   -> "P1a"
                                        [] self \in Acceptors -> "A"]

P1a(self) == /\ pc[self] = "P1a"
             /\ msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
             /\ pc' = [pc EXCEPT ![self] = "P2a"]
             /\ UNCHANGED << maxBal, maxVBal, maxVal >>

P2a(self) == /\ pc[self] = "P2a"
             /\ \E Q \in Quorums :
                  LET Q1b  == {m \in msgs : /\ m.type = "1b"
                                            /\ m.bal = self
                                            /\ m.acc \in Q}
                      Q1bv == {m \in Q1b : m.mbal >= 0}
                  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
                      /\ \E v \in Values :
                           /\ \/ Q1bv = {}
                              \/ \E m \in Q1bv :
                                   /\ m.mval = v
                                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
                           /\ msgs' = msgs \cup
                                 {[type |-> "2a", bal |-> self, val |-> v]}
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Proposer(self) == P1a(self) \/ P2a(self)

A(self) == /\ pc[self] = "A"
           /\ \E m \in msgs :
                \/ /\ m.type = "1a"
                   /\ m.bal > maxBal[self]
                   /\ maxBal' = [maxBal EXCEPT ![self] = m.bal]
                   /\ msgs' = msgs \cup
                         {[type |-> "1b", acc |-> self, bal |-> m.bal,
                           mbal |-> maxVBal[self], mval |-> maxVal[self]]}
                   /\ UNCHANGED << maxVBal, maxVal >>
                \/ /\ m.type = "2a"
                   /\ m.bal >= maxBal[self]
                   /\ maxBal'  = [maxBal  EXCEPT ![self] = m.bal]
                   /\ maxVBal' = [maxVBal EXCEPT ![self] = m.bal]
                   /\ maxVal'  = [maxVal  EXCEPT ![self] = m.val]
                   /\ msgs' = msgs \cup
                         {[type |-> "2b", acc |-> self,
                           bal |-> m.bal, val |-> m.val]}
           /\ pc' = [pc EXCEPT ![self] = "A"]

Acceptor(self) == A(self)

Next == \/ (\E self \in Ballots : Proposer(self))
        \/ (\E self \in Acceptors : Acceptor(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ msgs \subseteq Message
          /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVal  \in [Acceptors -> Values \cup {None}]
          /\ \A a \in Acceptors : maxVBal[a] =< maxBal[a]
          /\ pc \in [ProcSet -> {"P1a", "P2a", "A", "Done"}]

VotedFor(a, b, v) ==
    [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

OneValuePerBallot ==
    \A m1, m2 \in msgs :
        (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1.val = m2.val

THEOREM Spec => [](TypeOK /\ Consistency /\ OneValuePerBallot)
=============================================================================
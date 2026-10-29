------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Single-decree Paxos, written as a PlusCal algorithm and translated into  *)
(* TLA+.  Leaders (one per ballot) and acceptors communicate by adding      *)
(* message records to the set msgs.  Each acceptor tracks its highest       *)
(* prepared ballot (maxPrepared), its highest accepted ballot               *)
(* (maxAccepted) and the value accepted in that ballot (valAccepted).       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME /\ IsFiniteSet(Acceptors)
       /\ IsFiniteSet(Values)
       /\ Ballots \subseteq Nat
       /\ Quorums \subseteq SUBSET Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

(***************************************************************************
--algorithm Paxos
{ variables maxPrepared = [a \in Acceptors |-> -1],
            maxAccepted = [a \in Acceptors |-> -1],
            valAccepted = [a \in Acceptors |-> None],
            msgs = {};

  define {
    sentMsgs(t, b) == {m \in msgs : m.type = t /\ m.bal = b}
  }

  macro Send(m) { msgs := msgs \cup {m} }

  process (leader \in Ballots)
  { L: while (TRUE) {
         either { \* Phase 1a
           Send([type |-> "1a", bal |-> self])
         }
         or { \* Phase 2a
           await sentMsgs("2a", self) = {};
           with (Q \in Quorums,
                 S = {m \in sentMsgs("1b", self) : m.acc \in Q}) {
             await \A a \in Q : \E m \in S : m.acc = a;
             with (v \in Values) {
               await \/ \A m \in S : m.mbal = -1
                     \/ \E m \in S : /\ m.mval = v
                                     /\ \A mm \in S : mm.mbal =< m.mbal;
               Send([type |-> "2a", bal |-> self, val |-> v])
             }
           }
         }
       }
  }

  process (acceptor \in Acceptors)
  { A: while (TRUE) {
         either { \* Phase 1b
           with (m \in {mm \in msgs : mm.type = "1a" /\ mm.bal > maxPrepared[self]}) {
             maxPrepared[self] := m.bal;
             Send([type |-> "1b", acc |-> self, bal |-> m.bal,
                   mbal |-> maxAccepted[self], mval |-> valAccepted[self]])
           }
         }
         or { \* Phase 2b
           with (m \in {mm \in msgs : mm.type = "2a" /\ mm.bal >= maxPrepared[self]}) {
             maxPrepared[self] := m.bal;
             maxAccepted[self] := m.bal;
             valAccepted[self] := m.val;
             Send([type |-> "2b", acc |-> self, bal |-> m.bal, val |-> m.val])
           }
         }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxPrepared, maxAccepted, valAccepted, msgs

sentMsgs(t, b) == {m \in msgs : m.type = t /\ m.bal = b}

vars == << maxPrepared, maxAccepted, valAccepted, msgs >>

ProcSet == (Ballots) \cup (Acceptors)

Send(m) == msgs' = msgs \cup {m}

Init == /\ maxPrepared = [a \in Acceptors |-> -1]
        /\ maxAccepted = [a \in Acceptors |-> -1]
        /\ valAccepted = [a \in Acceptors |-> None]
        /\ msgs = {}

Phase1a(self) ==
    /\ Send([type |-> "1a", bal |-> self])
    /\ UNCHANGED << maxPrepared, maxAccepted, valAccepted >>

Phase2a(self) ==
    /\ sentMsgs("2a", self) = {}
    /\ \E Q \in Quorums :
         LET S == {m \in sentMsgs("1b", self) : m.acc \in Q}
         IN  /\ \A a \in Q : \E m \in S : m.acc = a
             /\ \E v \in Values :
                  /\ \/ \A m \in S : m.mbal = -1
                     \/ \E m \in S : /\ m.mval = v
                                     /\ \A mm \in S : mm.mbal =< m.mbal
                  /\ Send([type |-> "2a", bal |-> self, val |-> v])
    /\ UNCHANGED << maxPrepared, maxAccepted, valAccepted >>

leader(self) == Phase1a(self) \/ Phase2a(self)

Phase1b(self) ==
    \E m \in {mm \in msgs : mm.type = "1a" /\ mm.bal > maxPrepared[self]} :
      /\ maxPrepared' = [maxPrepared EXCEPT ![self] = m.bal]
      /\ Send([type |-> "1b", acc |-> self, bal |-> m.bal,
               mbal |-> maxAccepted[self], mval |-> valAccepted[self]])
      /\ UNCHANGED << maxAccepted, valAccepted >>

Phase2b(self) ==
    \E m \in {mm \in msgs : mm.type = "2a" /\ mm.bal >= maxPrepared[self]} :
      /\ maxPrepared' = [maxPrepared EXCEPT ![self] = m.bal]
      /\ maxAccepted' = [maxAccepted EXCEPT ![self] = m.bal]
      /\ valAccepted' = [valAccepted EXCEPT ![self] = m.val]
      /\ Send([type |-> "2b", acc |-> self, bal |-> m.bal, val |-> m.val])

acceptor(self) == Phase1b(self) \/ Phase2b(self)

Next == (\E self \in Ballots : leader(self))
           \/ (\E self \in Acceptors : acceptor(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

TypeOK ==
    /\ maxPrepared \in [Acceptors -> Ballots \cup {-1}]
    /\ maxAccepted \in [Acceptors -> Ballots \cup {-1}]
    /\ valAccepted \in [Acceptors -> Values \cup {None}]

ChosenIn(b, v) ==
    \E Q \in Quorums : \A a \in Q :
        \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

Chosen(v) == \E b \in Ballots : ChosenIn(b, v)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2
=============================================================================
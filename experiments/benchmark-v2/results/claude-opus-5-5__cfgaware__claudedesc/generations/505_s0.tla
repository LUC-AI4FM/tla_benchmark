------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Single-decree Paxos, written as a PlusCal algorithm and shown here in   *)
(* its translated TLA+ form. Leader election is omitted, and a single     *)
(* fixed proposer is assumed.                                              *)
(***************************************************************************)
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

None == 0

(* --algorithm Paxos
variables msgs = {},
          maxPrepared = [a \in Acceptors |-> -1],
          maxAccepted = [a \in Acceptors |-> -1],
          valAccepted = [a \in Acceptors |-> None];

process Proposer = "proposer"
begin
  P: while TRUE do
       either \* Phase 1a
         with b \in Ballots do
           await ~\E m \in msgs : m.type = "1a" /\ m.bal = b;
           msgs := msgs \cup {[type |-> "1a", bal |-> b]};
         end with;
       or \* Phase 2a
         with b \in Ballots, v \in Values, Q \in Quorums do
           ...
         end with;
       end either;
     end while;
end process;

process Acceptor \in Acceptors
begin
  A: while TRUE do
       either \* Phase 1b
         ...
       or \* Phase 2b
         ...
       end either;
     end while;
end process;
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES msgs, maxPrepared, maxAccepted, valAccepted

vars == << msgs, maxPrepared, maxAccepted, valAccepted >>

Send(m) == msgs' = msgs \cup {m}

Init == /\ msgs = {}
        /\ maxPrepared = [a \in Acceptors |-> -1]
        /\ maxAccepted = [a \in Acceptors |-> -1]
        /\ valAccepted = [a \in Acceptors |-> None]

Phase1a ==
  \E b \in Ballots :
    /\ ~\E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED << maxPrepared, maxAccepted, valAccepted >>

Phase2a ==
  \E b \in Ballots :
    /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b
    /\ \E v \in Values, Q \in Quorums :
         LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
         IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
             /\ \/ \A m \in Q1b : m.mbal = -1
                \/ \E m \in Q1b :
                     /\ m.mval = v
                     /\ \A m2 \in Q1b : m2.mbal <= m.mbal
             /\ Send([type |-> "2a", bal |-> b, val |-> v])
    /\ UNCHANGED << maxPrepared, maxAccepted, valAccepted >>

Proposer == Phase1a \/ Phase2a

Phase1b(self) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxPrepared[self]
    /\ maxPrepared' = [maxPrepared EXCEPT ![self] = m.bal]
    /\ Send([type |-> "1b", acc |-> self, bal |-> m.bal,
             mbal |-> maxAccepted[self], mval |-> valAccepted[self]])
    /\ UNCHANGED << maxAccepted, valAccepted >>

Phase2b(self) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxPrepared[self]
    /\ maxPrepared' = [maxPrepared EXCEPT ![self] = m.bal]
    /\ maxAccepted' = [maxAccepted EXCEPT ![self] = m.bal]
    /\ valAccepted' = [valAccepted EXCEPT ![self] = m.val]
    /\ Send([type |-> "2b", acc |-> self, bal |-> m.bal, val |-> m.val])

Acceptor(self) == Phase1b(self) \/ Phase2b(self)

Next == Proposer \/ (\E self \in Acceptors : Acceptor(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION
=============================================================================
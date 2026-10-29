------------------------------- MODULE Paxos -------------------------------
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
NoBallot == -1
ProposerId == "proposer"

(***************************************************************************
--algorithm Paxos {
  variables msgs = {},
            maxPrepared = [a \in Acceptors |-> -1],
            maxAccepted = [a \in Acceptors |-> -1],
            valAccepted = [a \in Acceptors |-> 0];

  process (Proposer = "proposer") {
    P: while (TRUE) {
         either Phase1a: with (b \in Ballots) { ... }
         or     Phase2a: with (b \in Ballots, v \in Values) { ... }
       }
  }

  process (Acceptor \in Acceptors) {
    A: while (TRUE) {
         either Phase1b: with (m \in msgs) { ... }
         or     Phase2b: with (m \in msgs) { ... }
       }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES msgs, maxPrepared, maxAccepted, valAccepted

vars == << msgs, maxPrepared, maxAccepted, valAccepted >>

ProcSet == {ProposerId} \cup Acceptors

Send(m) == msgs' = msgs \cup {m}

Init == /\ msgs = {}
        /\ maxPrepared = [a \in Acceptors |-> NoBallot]
        /\ maxAccepted = [a \in Acceptors |-> NoBallot]
        /\ valAccepted = [a \in Acceptors |-> None]

(***************************************************************************)
(* Proposer actions                                                        *)
(***************************************************************************)
Phase1a ==
    \E b \in Ballots :
        /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
        /\ Send([type |-> "1a", bal |-> b])
        /\ UNCHANGED << maxPrepared, maxAccepted, valAccepted >>

Phase2a ==
    \E b \in Ballots, v \in Values :
        /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
        /\ \E Q \in Quorums :
             LET M == {m \in msgs : /\ m.type = "1b"
                                    /\ m.bal = b
                                    /\ m.acc \in Q}
             IN  /\ \A a \in Q : \E m \in M : m.acc = a
                 /\ \/ \A m \in M : m.mbal = NoBallot
                    \/ \E m \in M :
                         /\ m.mval = v
                         /\ \A m2 \in M : m.mbal >= m2.mbal
        /\ Send([type |-> "2a", bal |-> b, val |-> v])
        /\ UNCHANGED << maxPrepared, maxAccepted, valAccepted >>

Proposer == Phase1a \/ Phase2a

(***************************************************************************)
(* Acceptor actions                                                        *)
(***************************************************************************)
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

Next == Proposer
           \/ (\E self \in Acceptors : Acceptor(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

=============================================================================
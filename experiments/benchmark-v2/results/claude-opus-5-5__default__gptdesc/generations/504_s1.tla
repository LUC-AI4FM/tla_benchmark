---------------------------- MODULE Paxos ----------------------------
(***************************************************************************)
(* Single-decree Paxos with a fixed leader and no leader election.         *)
(* Communication is modeled as a growing set of sent messages.  The state  *)
(* of each acceptor is given by maxPrepared, maxAccepted and valAccepted.  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors,   \* the set of acceptors
          Values,      \* the set of values that may be proposed
          Quorums,     \* the set of quorums
          Ballots      \* the set of ballot numbers

ASSUME AcceptorsFinite == IsFiniteSet(Acceptors)
ASSUME ValuesFinite    == IsFiniteSet(Values)
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME BallotAssumption == Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        maxAcc : Ballots \cup {-1}, maxVal : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES msgs,          \* set of all messages sent so far
          maxPrepared,   \* maxPrepared[a]: highest ballot a has promised
          maxAccepted,   \* maxAccepted[a]: highest ballot a has accepted
          valAccepted    \* valAccepted[a]: value accepted in maxAccepted[a]

vars == <<msgs, maxPrepared, maxAccepted, valAccepted>>

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

(***************************************************************************)
(* Phase 1a: the (fixed) leader starts ballot b by sending a prepare msg.  *)
(***************************************************************************)
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 1b: acceptor a promises not to accept lower ballots and reports   *)
(* the highest-numbered ballot it accepted and the corresponding value.    *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxPrepared[a]
    /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             maxAcc |-> maxAccepted[a], maxVal |-> valAccepted[a]])
    /\ UNCHANGED <<maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 2a: having received 1b messages from a quorum for ballot b, the   *)
(* leader proposes a value that is safe: either any value if no acceptor   *)
(* in the quorum has accepted anything, or the value accepted in the       *)
(* highest-numbered ballot reported.                                       *)
(***************************************************************************)
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
           Q1bv == {m \in Q1b : m.maxAcc >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                   /\ m.maxVal = v
                   /\ \A mm \in Q1bv : m.maxAcc >= mm.maxAcc
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 2b: acceptor a accepts the proposal of a 2a message whose ballot  *)
(* is at least as high as any ballot it has promised.                      *)
(***************************************************************************)
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxPrepared[a]
    /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
    /\ maxAccepted' = [maxAccepted EXCEPT ![a] = m.bal]
    /\ valAccepted' = [valAccepted EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
  \/ \E b \in Ballots : Phase1a(b) \/ \E v \in Values : Phase2a(b, v)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
VotedForIn(a, v, b) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.acc = a
                  /\ m.val = v
                  /\ m.bal = b

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

AcceptedConsistent ==
  \A a \in Acceptors :
     /\ maxAccepted[a] <= maxPrepared[a]
     /\ (maxAccepted[a] = -1) <=> (valAccepted[a] = None)

THEOREM Spec => [](TypeOK /\ Consistency /\ AcceptedConsistent)
=============================================================================
---------------------------- MODULE FixedLeaderPaxos ----------------------------
(***************************************************************************)
(* Single-decree Paxos with a fixed leader (no leader election).          *)
(* Communication is modeled as a monotonically growing set of sent        *)
(* messages.  Acceptor state is captured by maxPrepared, maxAccepted and  *)
(* valAccepted.                                                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME AcceptorsFinite == IsFiniteSet(Acceptors)
ASSUME ValuesFinite    == IsFiniteSet(Values)
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME BallotAssumption == Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

NoBallot == -1

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES msgs, maxPrepared, maxAccepted, valAccepted

vars == <<msgs, maxPrepared, maxAccepted, valAccepted>>

TypeOK ==
  /\ msgs \subseteq Message
  /\ maxPrepared \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxAccepted \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ valAccepted \in [Acceptors -> Values \cup {None}]

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ msgs = {}
  /\ maxPrepared = [a \in Acceptors |-> NoBallot]
  /\ maxAccepted = [a \in Acceptors |-> NoBallot]
  /\ valAccepted = [a \in Acceptors |-> None]

(***************************************************************************)
(* Phase 1a: the fixed leader starts ballot b by sending a prepare msg.  *)
(***************************************************************************)
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 1b: an acceptor promises not to accept lower ballots and reports *)
(* the highest-ballot value it has accepted.                              *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxPrepared[a]
    /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxAccepted[a], mval |-> valAccepted[a]])
    /\ UNCHANGED <<maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 2a: the leader, having 1b messages from a quorum for ballot b,   *)
(* proposes a safe value v.                                               *)
(***************************************************************************)
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                   /\ m.mval = v
                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts a proposal unless it has promised a      *)
(* higher ballot.                                                         *)
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
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E b \in Ballots, v \in Values : Phase2a(b, v)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
VotedFor(a, b, v) ==
  \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

AcceptedConsistent ==
  \A a \in Acceptors :
    /\ maxAccepted[a] <= maxPrepared[a]
    /\ (maxAccepted[a] = NoBallot) <=> (valAccepted[a] = None)

THEOREM Spec => [](TypeOK /\ Consistency /\ AcceptedConsistent)
=============================================================================
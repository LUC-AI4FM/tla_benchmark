------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Single-decree Paxos with a fixed leader and no leader election.         *)
(* Communication is a monotonically growing set of sent messages.          *)
(* Acceptor state: maxPrepared, maxAccepted, valAccepted.                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME AcceptorsFinite == IsFiniteSet(Acceptors)
ASSUME ValuesFinite    == IsFiniteSet(Values)
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME BallotsNat == Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES msgs, maxPrepared, maxAccepted, valAccepted

vars == <<msgs, maxPrepared, maxAccepted, valAccepted>>

TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxPrepared \in [Acceptors -> Ballots \cup {-1}]
  /\ maxAccepted \in [Acceptors -> Ballots \cup {-1}]
  /\ valAccepted \in [Acceptors -> Values \cup {None}]

Init ==
  /\ msgs = {}
  /\ maxPrepared = [a \in Acceptors |-> -1]
  /\ maxAccepted = [a \in Acceptors |-> -1]
  /\ valAccepted = [a \in Acceptors |-> None]

Send(m) == msgs' = msgs \cup {m}

(* Phase 1a: the (fixed) leader starts ballot b *)
Phase1a(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(* Phase 1b: acceptor a promises ballot m.bal *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxPrepared[a]
    /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxAccepted[a], mval |-> valAccepted[a]])
    /\ UNCHANGED <<maxAccepted, valAccepted>>

(* Phase 2a: leader proposes value v in ballot b *)
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

(* Phase 2b: acceptor a accepts a proposal *)
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

-----------------------------------------------------------------------------
(* Safety *)

VotedForIn(a, v, b) ==
  \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.val = v /\ m.bal = b

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

OneProposalPerBallot ==
  \A m1, m2 \in msgs :
    (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1.val = m2.val

AcceptedBelowPrepared ==
  \A a \in Acceptors : maxAccepted[a] <= maxPrepared[a]

THEOREM Spec => [](TypeOK /\ Consistency)
=============================================================================
------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Quorums, Values, Ballots

ASSUME AcceptorsAssumption ==
    /\ IsFiniteSet(Acceptors)
    /\ Cardinality(Acceptors) >= 3

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME ValuesAssumption ==
    /\ IsFiniteSet(Values)
    /\ Cardinality(Values) >= 2
    /\ Values \subseteq (Nat \ {0})

ASSUME BallotsAssumption ==
    /\ IsFiniteSet(Ballots)
    /\ Ballots \subseteq Nat

None == 0
NoBallot == -1

VARIABLES msgs,         \* set of all messages ever sent
          maxPrepared,  \* maxPrepared[a]: highest ballot seen in a 1a message
          maxAccepted,  \* maxAccepted[a]: highest ballot in which a voted (2b)
          valAccepted   \* valAccepted[a]: value voted for in ballot maxAccepted[a]

vars == <<msgs, maxPrepared, maxAccepted, valAccepted>>

Messages ==
         [type : {"1a"}, bal : Ballots]
    \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
          mbal : Ballots \cup {NoBallot}, mval : Values \cup {None}]
    \cup [type : {"2a"}, bal : Ballots, val : Values]
    \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

TypeOK ==
    /\ msgs \subseteq Messages
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
(* Phase 1a: the leader broadcasts a prepare message for a fresh ballot.   *)
(***************************************************************************)
Phase1a(b) ==
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 1b: an acceptor promises not to accept lower ballots and reports  *)
(* its highest prior vote.                                                  *)
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
(* Phase 2a: upon a quorum of promises for ballot b, the leader proposes   *)
(* the value of the highest-ballot vote reported, or any value if none.    *)
(***************************************************************************)
Phase2a(b, v) ==
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
    /\ \E Q \in Quorums :
         LET Q1b == {m \in msgs : /\ m.type = "1b"
                                  /\ m.bal = b
                                  /\ m.acc \in Q}
             Q1bv == {m \in Q1b : m.mbal >= 0}
         IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
             /\ \/ Q1bv = {}
                \/ \E m \in Q1bv :
                     /\ m.mval = v
                     /\ \A mm \in Q1bv : m.mbal >= mm.mbal
    /\ Send([type |-> "2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts a proposal unless it has promised a       *)
(* higher ballot.                                                           *)
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
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E b \in Ballots, v \in Values : Phase2a(b, v)
    \/ \E a \in Acceptors : Phase2b(a)

Spec == Init /\ [][Next]_vars

=============================================================================
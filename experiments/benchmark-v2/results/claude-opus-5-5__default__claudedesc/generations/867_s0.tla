------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Classic Paxos consensus with no explicit leader or learner roles.       *)
(* Four replicas act as both proposers and acceptors.  Quorums are any     *)
(* three-of-four majority subsets of the replicas.                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Ballots,   \* finite set of ballot numbers, including 0
          Values     \* finite set of proposable values

ASSUME Ballots \subseteq Nat /\ 0 \in Ballots
ASSUME IsFiniteSet(Values) /\ Values # {}

Replicas == {"r1", "r2", "r3", "r4"}

Quorums == {Q \in SUBSET Replicas : Cardinality(Q) = 3}

None == CHOOSE x : x \notin Values

VARIABLES messages,    \* global set of all messages ever sent
          maxBallot,   \* maxBallot[a]: highest ballot seen by acceptor a
          maxVBallot,  \* maxVBallot[a]: highest ballot in which a accepted a value
          maxValue,    \* maxValue[a]: value accepted by a in ballot maxVBallot[a]
          decision     \* any learnt value (None if nothing learnt yet)

vars == <<messages, maxBallot, maxVBallot, maxValue, decision>>

-----------------------------------------------------------------------------
Message ==
         [type : {"1a"}, bal : Ballots]
    \cup [type : {"1b"}, acc : Replicas, bal : Ballots,
          mbal : Ballots, mval : Values \cup {None}]
    \cup [type : {"2a"}, bal : Ballots, val : Values]
    \cup [type : {"2b"}, acc : Replicas, bal : Ballots, val : Values]

TypeOK ==
    /\ messages \subseteq Message
    /\ maxBallot \in [Replicas -> Ballots]
    /\ maxVBallot \in [Replicas -> Ballots]
    /\ maxValue \in [Replicas -> Values \cup {None}]
    /\ decision \in Values \cup {None}

Send(m) == messages' = messages \cup {m}

-----------------------------------------------------------------------------
Init ==
    /\ messages = {}
    /\ maxBallot = [a \in Replicas |-> 0]
    /\ maxVBallot = [a \in Replicas |-> 0]
    /\ maxValue = [a \in Replicas |-> None]
    /\ decision = None

(***************************************************************************)
(* Phase 1a: a proposer broadcasts a prepare for any nonzero ballot.       *)
(***************************************************************************)
PaxosPrepare ==
    \E b \in Ballots :
        /\ b # 0
        /\ Send([type |-> "1a", bal |-> b])
        /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

(***************************************************************************)
(* Phase 1b: an acceptor promises if the ballot exceeds its maximum.       *)
(***************************************************************************)
PaxosPromise ==
    \E a \in Replicas, m \in messages :
        /\ m.type = "1a"
        /\ m.bal > maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBallot[a], mval |-> maxValue[a]])
        /\ UNCHANGED <<maxVBallot, maxValue, decision>>

(***************************************************************************)
(* The value associated with the highest previously accepted ballot among  *)
(* a set S of Phase 1b messages.                                           *)
(***************************************************************************)
ForcedValue(S) ==
    LET withVal == {m \in S : m.mval # None}
    IN  (CHOOSE m \in withVal : \A m2 \in withVal : m.mbal >= m2.mbal).mval

(***************************************************************************)
(* Phase 2a: having heard Phase 1b from a full quorum, the proposer sends  *)
(* an accept carrying the forced value, or any value if none is forced.    *)
(***************************************************************************)
PaxosAccept ==
    \E b \in Ballots, Q \in Quorums, v \in Values :
        LET S == {m \in messages : /\ m.type = "1b"
                                   /\ m.bal = b
                                   /\ m.acc \in Q}
        IN  /\ b # 0
            /\ ~ \E m \in messages : m.type = "2a" /\ m.bal = b
            /\ \A a \in Q : \E m \in S : m.acc = a
            /\ IF \A m \in S : m.mval = None
                  THEN TRUE
                  ELSE v = ForcedValue(S)
            /\ Send([type |-> "2a", bal |-> b, val |-> v])
            /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts if the ballot is at least its maximum.    *)
(***************************************************************************)
PaxosAccepted ==
    \E a \in Replicas, m \in messages :
        /\ m.type = "2a"
        /\ m.bal >= maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.bal]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
        /\ UNCHANGED decision

(***************************************************************************)
(* Learning: a value is decided once a quorum sent matching Phase 2b.      *)
(***************************************************************************)
PaxosDecide ==
    \E b \in Ballots, v \in Values, Q \in Quorums :
        /\ \A a \in Q : \E m \in messages : /\ m.type = "2b"
                                            /\ m.acc = a
                                            /\ m.bal = b
                                            /\ m.val = v
        /\ decision' = v
        /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

Next ==
    \/ PaxosPrepare
    \/ PaxosPromise
    \/ PaxosAccept
    \/ PaxosAccepted
    \/ PaxosDecide

Spec == Init /\ [][Next]_vars /\ SF_vars(PaxosDecide)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)

\* Only proposed values may be learnt.
PaxosNontriviality ==
    decision = None \/ \E m \in messages : m.type = "2a" /\ m.val = decision

\* Once a value is learnt, the decision never changes.
PaxosConsistency ==
    [][decision # None => decision' = decision]_vars

(***************************************************************************)
(* Liveness cannot be guaranteed (FLP impossibility).                      *)
(***************************************************************************)
PaxosLiveness == FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []PaxosNontriviality
THEOREM Spec => PaxosConsistency
=============================================================================
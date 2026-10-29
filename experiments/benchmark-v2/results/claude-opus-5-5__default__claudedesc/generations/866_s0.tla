------------------------------ MODULE FastPaxos ------------------------------
(***************************************************************************)
(* A simplified specification of Leslie Lamport's Fast Paxos.              *)
(*                                                                         *)
(* Assumptions:                                                            *)
(*   - a unique coordinator, so Phase 1 is not needed,                     *)
(*   - full connectivity among all agents,                                 *)
(*   - stable storage for all replicas.                                    *)
(*                                                                         *)
(* The base Paxos definitions are written inline so that this module is    *)
(* self-contained: variables, message helpers, the classic Phase 2a and    *)
(* Phase 2b actions, and PaxosConsistency.                                 *)
(*                                                                         *)
(* Intended model:                                                         *)
(*   Replicas    <- {r1, r2, r3, r4}                                       *)
(*   Values      <- {v1, v2, v3}                                           *)
(*   Ballots     <- {1, 2, 3, 4, 5}                                        *)
(*   FastBallots <- {1, 3}                                                 *)
(*   Quorums     <- all size-3 subsets of Replicas                         *)
(*   FastQuorums <- all size-3 subsets of Replicas                         *)
(*   none, any   <- model values                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Replicas,      \* The set of acceptors/replicas.
          Values,        \* The set of values that may be proposed.
          Ballots,       \* The set of ballot numbers.
          Quorums,       \* The classic quorums.
          FastQuorums,   \* The fast quorums.
          FastBallots,   \* The ballots that are fast rounds.
          none,          \* Placeholder meaning "no value".
          any            \* The special "any" value of a fast-round P2a.

ASSUME PaxosAssume ==
    /\ Ballots \subseteq Nat \ {0}
    /\ Quorums \subseteq SUBSET Replicas
    /\ \A q1, q2 \in Quorums : q1 \cap q2 # {}
    /\ none \notin Values
    /\ any \notin Values
    /\ any # none

ASSUME FastAssume ==
    /\ FastBallots \subseteq Ballots
    /\ FastQuorums \subseteq SUBSET Replicas
    /\ \A q \in Quorums, f1, f2 \in FastQuorums : q \cap f1 \cap f2 # {}
    /\ \A f1, f2, f3 \in FastQuorums : f1 \cap f2 \cap f3 # {}

ClassicBallots == Ballots \ FastBallots

-----------------------------------------------------------------------------
(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)
VARIABLES messages,    \* The set of all messages that have been sent.
          decision,    \* The decided value, or none.
          maxBallot,   \* maxBallot[a]: highest ballot acceptor a took part in.
          maxVBallot,  \* maxVBallot[a]: highest ballot in which a voted.
          maxValue,    \* maxValue[a]: the value a voted for in maxVBallot[a].
          cValue       \* The coordinator's value chosen during recovery.

paxosVars == <<messages, decision, maxBallot, maxVBallot, maxValue>>
vars      == <<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>

P2aMessage == [type : {"P2a"}, ballot : Ballots, value : Values \cup {any}]
P2bMessage == [type : {"P2b"}, ballot : Ballots, acceptor : Replicas,
               value : Values]
Message    == P2aMessage \cup P2bMessage

p2aMessages == {m \in messages : m.type = "P2a"}
p2bMessages == {m \in messages : m.type = "P2b"}

SendMessage(m) == messages' = messages \cup {m}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)
TypeOK ==
    /\ messages \subseteq Message
    /\ decision \in Values \cup {none}
    /\ maxBallot \in [Replicas -> Ballots \cup {0}]
    /\ maxVBallot \in [Replicas -> Ballots \cup {0}]
    /\ maxValue \in [Replicas -> Values \cup {none}]

FastTypeOK ==
    /\ TypeOK
    /\ cValue \in Values \cup {none}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ messages = {}
    /\ decision = none
    /\ maxBallot = [a \in Replicas |-> 0]
    /\ maxVBallot = [a \in Replicas |-> 0]
    /\ maxValue = [a \in Replicas |-> none]

FastInit ==
    /\ Init
    /\ cValue = none

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fast rounds                                                             *)
(***************************************************************************)

(* The coordinator broadcasts the special "any" P2a for a fast ballot.     *)
FastAny ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E f \in FastBallots :
        /\ \A m \in p2aMessages : m.ballot # f
        /\ SendMessage([type |-> "P2a", ballot |-> f, value |-> any])

(* An acceptor receiving an "any" message proposes its own value directly *)
(* in a P2b reply.                                                         *)
FastPropose ==
    /\ UNCHANGED <<decision, cValue>>
    /\ \E a \in Replicas, m \in p2aMessages, v \in Values :
        /\ m.value = any
        /\ maxBallot[a] <= m.ballot
        /\ \A n \in p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ maxBallot'  = [maxBallot  EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue'   = [maxValue   EXCEPT ![a] = v]
        /\ SendMessage([type |-> "P2b", ballot |-> m.ballot,
                        acceptor |-> a, value |-> v])

(* A fast decision: an entire fast quorum agrees on a single value.       *)
FastDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Values : \E m \in M : m.value = w}
        IN  /\ \A a \in q : \E m \in M : m.acceptor = a
            /\ Cardinality(V) = 1
            /\ \E m \in M : decision' = m.value

-----------------------------------------------------------------------------
(***************************************************************************)
(* Classic rounds (collision recovery)                                     *)
(***************************************************************************)

(* Phase 2a. After a collision in fast ballot f, the coordinator picks the *)
(* majority value among the fast-quorum responses if there is one, and    *)
(* otherwise any proposed value. It then sends a classic P2a message.     *)
ClassicAccept ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, f \in FastBallots, q \in FastQuorums,
          v \in Values :
        /\ f < b
        /\ cValue = none \/ cValue = v
        /\ \A m \in p2aMessages : m.ballot # b
        /\ LET M   == {m \in p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V   == {w \in Values : \E m \in M : m.value = w}
               Maj == {w \in V :
                         2 * Cardinality({m \in M : m.value = w})
                             > Cardinality(q)}
           IN  /\ \A a \in q : \E m \in M : m.acceptor = a
               /\ Cardinality(V) > 1
               /\ IF Maj # {} THEN v \in Maj ELSE v \in V
        /\ cValue' = v
        /\ SendMessage([type |-> "P2a", ballot |-> b, value |-> v])

(* Phase 2b. An acceptor accepts a classic P2a message.                    *)
ClassicAccepted ==
    /\ UNCHANGED <<decision, cValue>>
    /\ \E a \in Replicas, m \in p2aMessages :
        /\ m.value # any
        /\ m.ballot \in ClassicBallots
        /\ maxBallot[a] <= m.ballot
        /\ \A n \in p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ maxBallot'  = [maxBallot  EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue'   = [maxValue   EXCEPT ![a] = m.value]
        /\ SendMessage([type |-> "P2b", ballot |-> m.ballot,
                        acceptor |-> a, value |-> m.value])

(* A classic decision: a classic quorum accepts in the same ballot.        *)
ClassicDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in ClassicBallots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN  /\ \A a \in q : \E m \in M : m.acceptor = a
            /\ \E m \in M : decision' = m.value

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
FastNext ==
    \/ FastAny
    \/ FastPropose
    \/ FastDecide
    \/ ClassicAccept
    \/ ClassicAccepted
    \/ ClassicDecide

FastSpec ==
    /\ FastInit
    /\ [][FastNext]_vars
    /\ SF_vars(FastDecide)
    /\ SF_vars(ClassicDecide)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* Nontriviality: only proposed values can be decided. Every value is     *)
(* proposed by an acceptor in a fast round.                                *)
FastNontriviality ==
    \/ decision = none
    \/ \E m \in p2bMessages : m.ballot \in FastBallots /\ m.value = decision

(* Consistency: at most one value is ever decided. Once a decision is     *)
(* made, it never changes.                                                 *)
PaxosConsistency ==
    [][decision # none => decision' = decision]_vars

THEOREM FastSpec => [](FastTypeOK /\ FastNontriviality)
THEOREM FastSpec => PaxosConsistency
=============================================================================
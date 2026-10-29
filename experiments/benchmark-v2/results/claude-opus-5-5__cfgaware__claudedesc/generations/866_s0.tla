------------------------------- MODULE FastPaxos -------------------------------
(***************************************************************************)
(* A simplified Fast Paxos specification. It assumes a unique coordinator, *)
(* so Phase 1 is not modeled. It also assumes full connectivity among      *)
(* agents and stable storage for all replicas.                             *)
(*                                                                         *)
(* In a fast round the coordinator broadcasts an "any" P2a message.        *)
(* Acceptors then propose their own values directly in P2b messages. A     *)
(* fast decision happens when a whole fast quorum votes for one value in   *)
(* one fast ballot.                                                        *)
(*                                                                         *)
(* On a collision, a later classic round picks a value. It takes the       *)
(* majority value among the fast quorum's responses if there is one, and   *)
(* any proposed value otherwise. It then runs the usual Phase 2a/2b.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS any, none,
          r1, r2, r3, r4,
          v1, v2, v3,
          Replicas, Values, Ballots, FastBallots, Quorums, FastQuorums

ASSUME /\ Ballots \subseteq Nat
       /\ FastBallots \subseteq Ballots
       /\ any \notin Values
       /\ none \notin Values
       /\ any # none
       /\ \A q \in Quorums : q \subseteq Replicas
       /\ \A q \in FastQuorums : q \subseteq Replicas

ClassicBallots == Ballots \ FastBallots

NoBallot == -1

VARIABLES messages,    \* set of all messages sent
          decision,    \* set of decided values
          maxBallot,   \* highest ballot each replica has participated in
          maxVBallot,  \* highest ballot in which each replica has voted
          maxValue,    \* value voted by each replica in maxVBallot
          cValue       \* value chosen by the coordinator on collision recovery

vars == <<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>

-----------------------------------------------------------------------------
P2aMessage == [type : {"P2a"}, ballot : Ballots, value : Values \cup {any}]
P2bMessage == [type : {"P2b"}, ballot : Ballots, acceptor : Replicas,
               value : Values]
Message == P2aMessage \cup P2bMessage

p2aMessages == {m \in messages : m.type = "P2a"}
p2bMessages == {m \in messages : m.type = "P2b"}

SendMessage(m) == messages' = messages \cup {m}

IsMajorityValue(M, v) ==
    Cardinality(M) \div 2 < Cardinality({m \in M : m.value = v})

-----------------------------------------------------------------------------
FastTypeOK ==
    /\ messages \subseteq Message
    /\ decision \subseteq Values
    /\ maxBallot \in [Replicas -> Ballots \cup {NoBallot}]
    /\ maxVBallot \in [Replicas -> Ballots \cup {NoBallot}]
    /\ maxValue \in [Replicas -> Values \cup {none}]
    /\ cValue \in Values \cup {none}

FastInit ==
    /\ messages = {}
    /\ decision = {}
    /\ maxBallot = [a \in Replicas |-> NoBallot]
    /\ maxVBallot = [a \in Replicas |-> NoBallot]
    /\ maxValue = [a \in Replicas |-> none]
    /\ cValue = none

-----------------------------------------------------------------------------
(* Fast round: the coordinator sends a special "any" P2a message. *)
FastAny ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E f \in FastBallots :
        /\ ~ \E m \in p2aMessages : m.ballot = f
        /\ SendMessage([type |-> "P2a", ballot |-> f, value |-> any])

(* Fast round: an acceptor proposes its own value directly in a P2b. *)
FastPropose ==
    /\ UNCHANGED <<decision, cValue>>
    /\ \E a \in Replicas, m \in p2aMessages, v \in Values :
        /\ m.value = any
        /\ maxBallot[a] <= m.ballot
        /\ maxValue[a] = none \/ maxValue[a] = v
        /\ ~ \E t \in p2bMessages : t.ballot = m.ballot /\ t.acceptor = a
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = v]
        /\ SendMessage([type |-> "P2b", ballot |-> m.ballot,
                        acceptor |-> a, value |-> v])

(* Fast decision: a whole fast quorum votes for one value in a fast ballot. *)
FastDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Values : \E m \in M : m.value = w}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ Cardinality(V) = 1
           /\ \E w \in V : decision' = decision \cup {w}

(* Collision recovery: the coordinator starts a classic round and picks  *)
(* the majority value among the fast quorum's responses if one exists,   *)
(* and any proposed value otherwise.                                     *)
ClassicAccept ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, f \in FastBallots, q \in FastQuorums,
          v \in Values :
        /\ f < b
        /\ cValue = none \/ cValue = v
        /\ ~ \E m \in p2aMessages : m.ballot = b
        /\ LET M == {m \in p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V == {w \in Values : \E m \in M : m.value = w}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ 1 < Cardinality(V)
              /\ IF \E w \in V : IsMajorityValue(M, w)
                    THEN IsMajorityValue(M, v)
                    ELSE v \in V
        /\ cValue' = v
        /\ SendMessage([type |-> "P2a", ballot |-> b, value |-> v])

(* Classic Phase 2b: an acceptor accepts the coordinator's value. *)
ClassicAccepted ==
    /\ UNCHANGED <<decision, cValue>>
    /\ \E a \in Replicas, m \in p2aMessages :
        /\ m.ballot \in ClassicBallots
        /\ m.value \in Values
        /\ maxBallot[a] <= m.ballot
        /\ ~ \E t \in p2bMessages : t.ballot = m.ballot /\ t.acceptor = a
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.value]
        /\ SendMessage([type |-> "P2b", ballot |-> m.ballot,
                        acceptor |-> a, value |-> m.value])

(* Classic decision: a classic quorum votes in the same classic ballot. *)
ClassicDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in ClassicBallots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = decision \cup {m.value}

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
(* Only proposed values can be decided. *)
FastNontriviality ==
    \A v \in decision : \E m \in p2bMessages : m.value = v

(* At most one value is ever decided. *)
PaxosConsistency ==
    \A x, y \in decision : x = y

PaxosSymmetry == Permutations(Replicas) \cup Permutations(Values)

=============================================================================
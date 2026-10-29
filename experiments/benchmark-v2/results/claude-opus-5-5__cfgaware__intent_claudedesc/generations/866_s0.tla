---------------------------- MODULE FastPaxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS any, none,
          r1, r2, r3, r4, Replicas,
          v1, v2, v3, Values,
          Ballots, FastBallots,
          Quorums, FastQuorums

ClassicBallots == Ballots \ FastBallots

ASSUME /\ any \notin Values
       /\ none \notin Values
       /\ any # none
       /\ FastBallots \subseteq Ballots
       /\ Ballots \subseteq Nat

ASSUME /\ \A Q \in Quorums : Q \subseteq Replicas
       /\ \A Q \in FastQuorums : Q \subseteq Replicas
       /\ \A F1, F2 \in FastQuorums : F1 \cap F2 # {}
       /\ \A F \in FastQuorums : 4 * Cardinality(F) >= 3 * Cardinality(Replicas)
       /\ \A Q \in Quorums : \A F1, F2 \in FastQuorums : Q \cap F1 \cap F2 # {}

VARIABLES msgs, maxBallot, maxVBallot, maxVValue, decision

vars == <<msgs, maxBallot, maxVBallot, maxVValue, decision>>

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

P1aMsgs == [type : {"P1a"}, bal : Ballots]
P1bMsgs == [type : {"P1b"}, acc : Replicas, bal : Ballots,
            vbal : Ballots \cup {-1}, vval : Values \cup {none}]
P2aMsgs == [type : {"P2a"}, bal : Ballots, val : Values \cup {any}]
P2bMsgs == [type : {"P2b"}, acc : Replicas, bal : Ballots, val : Values]

Messages == P1aMsgs \cup P1bMsgs \cup P2aMsgs \cup P2bMsgs

FastTypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBallot \in [Replicas -> Ballots \cup {-1}]
    /\ maxVBallot \in [Replicas -> Ballots \cup {-1}]
    /\ maxVValue \in [Replicas -> Values \cup {none}]
    /\ decision \subseteq Values

Send(m) == msgs' = msgs \cup {m}

(* Values proposed (voted for) by acceptors in fast rounds *)
FastProposed == {m.val : m \in {mm \in msgs : mm.type = "P2b" /\ mm.bal \in FastBallots}}

FastInit ==
    /\ msgs = {}
    /\ maxBallot = [a \in Replicas |-> -1]
    /\ maxVBallot = [a \in Replicas |-> -1]
    /\ maxVValue = [a \in Replicas |-> none]
    /\ decision = {}

(* Coordinator starts phase 1 of ballot b *)
Phase1a(b) ==
    /\ [type |-> "P1a", bal |-> b] \notin msgs
    /\ Send([type |-> "P1a", bal |-> b])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxVValue, decision>>

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "P1a"
        /\ m.bal > maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ Send([type |-> "P1b", acc |-> a, bal |-> m.bal,
                 vbal |-> maxVBallot[a], vval |-> maxVValue[a]])
        /\ UNCHANGED <<maxVBallot, maxVValue, decision>>

(* Coordinator phase 2a: fast "any" message, or collision recovery / classic value *)
Phase2a(b) ==
    /\ ~ \E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ \E Q \in Quorums :
        LET S == {m \in msgs : m.type = "P1b" /\ m.bal = b /\ m.acc \in Q}
        IN /\ \A a \in Q : \E m \in S : m.acc = a
           /\ LET k == Max({m.vbal : m \in S})
                  V == {m.vval : m \in {mm \in S : mm.vbal = k}}
                  W == {w \in V :
                          \E R \in FastQuorums :
                             \A a \in R \cap Q :
                                \E m \in S : m.acc = a /\ m.vbal = k /\ m.vval = w}
              IN \E v \in Values \cup {any} :
                   /\ IF k = -1
                        THEN IF b \in FastBallots
                               THEN v = any
                               ELSE v \in FastProposed
                        ELSE IF k \in ClassicBallots
                               THEN v \in V
                               ELSE IF W # {} THEN v \in W ELSE v \in V
                   /\ Send([type |-> "P2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxVValue, decision>>

(* Acceptor votes; in a fast round with "any" it votes for its own proposal *)
Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "P2a"
        /\ m.bal >= maxBallot[a]
        /\ maxVBallot[a] < m.bal
        /\ \E v \in Values :
             /\ IF m.val = any THEN m.bal \in FastBallots ELSE v = m.val
             /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
             /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.bal]
             /\ maxVValue' = [maxVValue EXCEPT ![a] = v]
             /\ Send([type |-> "P2b", acc |-> a, bal |-> m.bal, val |-> v])
        /\ UNCHANGED decision

VotedBy(Q, b, v) == \A a \in Q : [type |-> "P2b", acc |-> a, bal |-> b, val |-> v] \in msgs

FastDecide ==
    \E b \in FastBallots, Q \in FastQuorums, v \in Values :
        /\ VotedBy(Q, b, v)
        /\ v \notin decision
        /\ decision' = decision \cup {v}
        /\ UNCHANGED <<msgs, maxBallot, maxVBallot, maxVValue>>

ClassicDecide ==
    \E b \in ClassicBallots, Q \in Quorums, v \in Values :
        /\ VotedBy(Q, b, v)
        /\ v \notin decision
        /\ decision' = decision \cup {v}
        /\ UNCHANGED <<msgs, maxBallot, maxVBallot, maxVValue>>

FastNext ==
    \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
    \/ \E a \in Replicas : Phase1b(a) \/ Phase2b(a)
    \/ FastDecide
    \/ ClassicDecide

FastSpec == /\ FastInit
            /\ [][FastNext]_vars
            /\ WF_vars(FastDecide)
            /\ WF_vars(ClassicDecide)

(* Agreement: at most one value is decided *)
PaxosConsistency == \A x, y \in decision : x = y

(* Non-triviality: decided values were proposed by an acceptor in a fast round *)
FastNontriviality ==
    \A x \in decision :
        \E m \in msgs : m.type = "P2b" /\ m.bal \in FastBallots /\ m.val = x

Liveness ==
    /\ []((ENABLED FastDecide) => <>(decision # {}))
    /\ []((ENABLED ClassicDecide) => <>(decision # {}))

PaxosSymmetry == Permutations(Replicas) \cup Permutations(Values)

=============================================================================
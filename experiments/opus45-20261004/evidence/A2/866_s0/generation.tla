---------------------------- MODULE FastPaxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Replicas,
    Values,
    Ballots,
    FastBallots,
    ClassicQuorums,
    FastQuorums

VARIABLES
    maxBal,
    maxVBal,
    maxVal,
    msgs,
    decided,
    cValue

vars == <<maxBal, maxVBal, maxVal, msgs, decided, cValue>>

None == CHOOSE v : v \notin Values

IsFastBallot(b) == b \in FastBallots

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* Type definitions *)

Message ==
    [type : {"P2a"}, bal : Ballots, val : Values \cup {"any"}]
    \cup
    [type : {"P2b"}, bal : Ballots, val : Values, acc : Replicas]
    \cup
    [type : {"Decision"}, bal : Ballots, val : Values]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ maxBal = [a \in Replicas |-> 0]
    /\ maxVBal = [a \in Replicas |-> 0]
    /\ maxVal = [a \in Replicas |-> None]
    /\ msgs = {}
    /\ decided = {}
    /\ cValue = None

-----------------------------------------------------------------------------
(* Phase 2a actions *)

Phase2a(b, v) ==
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ IF IsFastBallot(b)
       THEN /\ v = "any"
            /\ Send([type |-> "P2a", bal |-> b, val |-> "any"])
       ELSE /\ v \in Values
            /\ Send([type |-> "P2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided, cValue>>

(* Phase 2b actions for acceptors *)

Phase2b(a, b, v) ==
    /\ maxBal[a] <= b
    /\ \E m \in msgs : m.type = "P2a" /\ m.bal = b /\
       (IF m.val = "any" THEN v \in Values ELSE v = m.val)
    /\ ~\E m \in msgs : m.type = "P2b" /\ m.bal = b /\ m.acc = a
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = v]
    /\ Send([type |-> "P2b", bal |-> b, val |-> v, acc |-> a])
    /\ UNCHANGED <<decided, cValue>>

-----------------------------------------------------------------------------
(* Fast decision: all members of a fast quorum vote for same value *)

FastDecide ==
    \E b \in FastBallots :
    \E Q \in FastQuorums :
    \E v \in Values :
        /\ \A a \in Q : \E m \in msgs : m.type = "P2b" /\ m.bal = b /\ m.acc = a /\ m.val = v
        /\ decided' = decided \cup {v}
        /\ Send([type |-> "Decision", bal |-> b, val |-> v])
        /\ UNCHANGED <<maxBal, maxVBal, maxVal, cValue>>

-----------------------------------------------------------------------------
(* Classic decision: all members of a classic quorum vote for same value in non-fast ballot *)

ClassicDecide ==
    \E b \in Ballots \ FastBallots :
    \E Q \in ClassicQuorums :
    \E v \in Values :
        /\ \A a \in Q : \E m \in msgs : m.type = "P2b" /\ m.bal = b /\ m.acc = a /\ m.val = v
        /\ decided' = decided \cup {v}
        /\ Send([type |-> "Decision", bal |-> b, val |-> v])
        /\ UNCHANGED <<maxBal, maxVBal, maxVal, cValue>>

-----------------------------------------------------------------------------
(* Collision recovery: coordinator chooses value for classic round after fast round collision *)

CollisionRecovery(b) ==
    /\ b \in Ballots \ FastBallots
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ \E fb \in FastBallots :
       \E Q \in FastQuorums :
           LET p2bMsgs == {m \in msgs : m.type = "P2b" /\ m.bal = fb /\ m.acc \in Q}
               votedValues == {m.val : m \in p2bMsgs}
               ValueCount(val) == Cardinality({m \in p2bMsgs : m.val = val})
               majorityVal == CHOOSE val \in votedValues :
                   \A val2 \in votedValues : ValueCount(val) >= ValueCount(val2)
           IN
           /\ Cardinality(p2bMsgs) = Cardinality(Q)
           /\ Cardinality(votedValues) > 1
           /\ cValue' = majorityVal
           /\ Send([type |-> "P2a", bal |-> b, val |-> majorityVal])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided>>

-----------------------------------------------------------------------------
(* Start a fast round *)

StartFastRound(b) ==
    /\ b \in FastBallots
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ Send([type |-> "P2a", bal |-> b, val |-> "any"])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided, cValue>>

(* Start a classic round with a specific value *)

StartClassicRound(b, v) ==
    /\ b \in Ballots \ FastBallots
    /\ v \in Values
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ Send([type |-> "P2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided, cValue>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E b \in FastBallots : StartFastRound(b)
    \/ \E b \in Ballots \ FastBallots : \E v \in Values : StartClassicRound(b, v)
    \/ \E a \in Replicas : \E b \in Ballots : \E v \in Values : Phase2b(a, b, v)
    \/ FastDecide
    \/ ClassicDecide
    \/ \E b \in Ballots \ FastBallots : CollisionRecovery(b)

-----------------------------------------------------------------------------
(* Fairness and specification *)

Fairness ==
    /\ SF_vars(FastDecide)
    /\ SF_vars(ClassicDecide)

FastSpec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Type invariant *)

FastTypeOK ==
    /\ maxBal \in [Replicas -> Ballots \cup {0}]
    /\ maxVBal \in [Replicas -> Ballots \cup {0}]
    /\ maxVal \in [Replicas -> Values \cup {None}]
    /\ msgs \subseteq Message
    /\ decided \subseteq Values
    /\ cValue \in Values \cup {None}

-----------------------------------------------------------------------------
(* Safety invariants *)

ProposedValues ==
    {m.val : m \in {msg \in msgs : msg.type = "P2b"}}

FastNontriviality ==
    decided \subseteq ProposedValues

PaxosConsistency ==
    Cardinality(decided) <= 1

-----------------------------------------------------------------------------
(* Specification *)

Spec == FastSpec

=============================================================================
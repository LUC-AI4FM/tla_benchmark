-------------------------------- MODULE FastPaxos --------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Acceptors,      \* The set of acceptors
    Values,         \* The set of proposable values
    Quorum,         \* Set of classic quorums
    FastQuorum,     \* Set of fast quorums
    Coordinator     \* The unique coordinator

VARIABLES
    proposed,       \* Set of values that have been proposed
    cBal,           \* Coordinator's current ballot
    cVal,           \* Coordinator's current value
    aBal,           \* aBal[a] = current ballot of acceptor a
    aVBal,          \* aVBal[a] = ballot in which acceptor a last voted
    aVal,           \* aVal[a] = value acceptor a last voted for
    sentMsgs,       \* Set of all sent messages
    learned         \* Set of values that have been learned (consensus reached)

vars == <<proposed, cBal, cVal, aBal, aVBal, aVal, sentMsgs, learned>>

None == CHOOSE v : v \notin Values
Ballots == Nat

\* Fast ballots are even, classic ballots are odd
IsFastBallot(b) == b % 2 = 0
IsClassicBallot(b) == b % 2 = 1

\* Message types
Message ==
    [type : {"1a"}, bal : Ballots]
    \cup
    [type : {"1b"}, acc : Acceptors, bal : Ballots, vbal : Ballots \cup {-1}, val : Values \cup {None}]
    \cup
    [type : {"2a"}, bal : Ballots, val : Values]
    \cup
    [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

TypeInvariant ==
    /\ proposed \subseteq Values
    /\ cBal \in Ballots
    /\ cVal \in Values \cup {None}
    /\ aBal \in [Acceptors -> Ballots \cup {-1}]
    /\ aVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ aVal \in [Acceptors -> Values \cup {None}]
    /\ sentMsgs \subseteq Message
    /\ learned \subseteq Values

\* Quorum assumptions
ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum : Q \subseteq Acceptors
    /\ \A Q \in FastQuorum : Q \subseteq Acceptors
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
    /\ \A Q \in Quorum : \A FQ \in FastQuorum : Q \cap FQ # {}
    /\ \A FQ1, FQ2, FQ3 \in FastQuorum : FQ1 \cap FQ2 \cap FQ3 # {}

Send(m) == sentMsgs' = sentMsgs \cup {m}

\* Phase 1a: Coordinator sends prepare message for a new ballot
Phase1a(b) ==
    /\ b > cBal
    /\ cBal' = b
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<proposed, cVal, aBal, aVBal, aVal, learned>>

\* Phase 1b: Acceptor responds to prepare message
Phase1b(a) ==
    \E m \in sentMsgs :
        /\ m.type = "1a"
        /\ m.bal > aBal[a]
        /\ aBal' = [aBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, vbal |-> aVBal[a], val |-> aVal[a]])
        /\ UNCHANGED <<proposed, cBal, cVal, aVBal, aVal, learned>>

\* Pick a value from 1b messages for phase 2a
PickValue(Q, b) ==
    LET msgs1b == {m \in sentMsgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
        maxVBal == LET vbals == {m.vbal : m \in msgs1b}
                   IN IF vbals = {} \/ vbals = {-1} THEN -1
                      ELSE CHOOSE vb \in vbals : \A vb2 \in vbals : vb >= vb2
        msgsWithMaxVBal == {m \in msgs1b : m.vbal = maxVBal}
        vals == {m.val : m \in msgsWithMaxVBal}
    IN IF maxVBal = -1 THEN None
       ELSE IF Cardinality(vals \ {None}) = 1 
            THEN CHOOSE v \in vals : v # None
            ELSE None

\* Phase 2a (Classic): Coordinator sends accept message after receiving quorum of 1b messages
Phase2aClassic(b) ==
    /\ IsClassicBallot(b)
    /\ cBal = b
    /\ \E Q \in Quorum :
        /\ \A a \in Q : \E m \in sentMsgs : m.type = "1b" /\ m.acc = a /\ m.bal = b
        /\ LET v == PickValue(Q, b)
           IN IF v # None
              THEN /\ cVal' = v
                   /\ Send([type |-> "2a", bal |-> b, val |-> v])
              ELSE \E val \in proposed :
                   /\ cVal' = val
                   /\ Send([type |-> "2a", bal |-> b, val |-> val])
    /\ UNCHANGED <<proposed, cBal, aBal, aVBal, aVal, learned>>

\* Phase 2a (Fast): Coordinator sends "any" message allowing acceptors to choose
Phase2aFast(b) ==
    /\ IsFastBallot(b)
    /\ cBal = b
    /\ \E Q \in Quorum :
        /\ \A a \in Q : \E m \in sentMsgs : m.type = "1b" /\ m.acc = a /\ m.bal = b
        /\ LET v == PickValue(Q, b)
           IN v = None
    /\ \E val \in proposed :
        /\ cVal' = val
        /\ Send([type |-> "2a", bal |-> b, val |-> val])
    /\ UNCHANGED <<proposed, cBal, aBal, aVBal, aVal, learned>>

\* Propose a value
Propose(v) ==
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED <<cBal, cVal, aBal, aVBal, aVal, sentMsgs, learned>>

\* Phase 2b (Classic): Acceptor accepts a value in a classic round
Phase2bClassic(a) ==
    \E m \in sentMsgs :
        /\ m.type = "2a"
        /\ IsClassicBallot(m.bal)
        /\ m.bal >= aBal[a]
        /\ aBal' = [aBal EXCEPT ![a] = m.bal]
        /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
        /\ aVal' = [aVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
        /\ UNCHANGED <<proposed, cBal, cVal, learned>>

\* Phase 2b (Fast): Acceptor votes directly for a proposed value in a fast round
Phase2bFast(a, v) ==
    \E m \in sentMsgs :
        /\ m.type = "2a"
        /\ IsFastBallot(m.bal)
        /\ m.bal >= aBal[a]
        /\ v \in proposed
        /\ aBal' = [aBal EXCEPT ![a] = m.bal]
        /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
        /\ aVal' = [aVal EXCEPT ![a] = v]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> v])
        /\ UNCHANGED <<proposed, cBal, cVal, learned>>

\* Learning: A value is learned when a quorum of acceptors have voted for it
Learn ==
    \E b \in Ballots :
        \E v \in Values :
            \/ /\ IsClassicBallot(b)
               /\ \E Q \in Quorum :
                    \A a \in Q : \E m \in sentMsgs :
                        /\ m.type = "2b"
                        /\ m.acc = a
                        /\ m.bal = b
                        /\ m.val = v
               /\ learned' = learned \cup {v}
               /\ UNCHANGED <<proposed, cBal, cVal, aBal, aVBal, aVal, sentMsgs>>
            \/ /\ IsFastBallot(b)
               /\ \E FQ \in FastQuorum :
                    \A a \in FQ : \E m \in sentMsgs :
                        /\ m.type = "2b"
                        /\ m.acc = a
                        /\ m.bal = b
                        /\ m.val = v
               /\ learned' = learned \cup {v}
               /\ UNCHANGED <<proposed, cBal, cVal, aBal, aVBal, aVal, sentMsgs>>

\* Recovery after collision in fast round - coordinator picks value
CoordinatorRecovery(b) ==
    /\ IsFastBallot(b)
    /\ b = cBal
    /\ \E Q \in Quorum :
        LET msgs2b == {m \in sentMsgs : m.type = "2b" /\ m.acc \in Q /\ m.bal = b}
            vals == {m.val : m \in msgs2b}
        IN /\ Cardinality(vals) > 1  \* Collision detected
           /\ \E v \in vals :
               /\ cVal' = v
               /\ Send([type |-> "2a", bal |-> b + 1, val |-> v])
               /\ cBal' = b + 1
    /\ UNCHANGED <<proposed, aBal, aVBal, aVal, learned>>

Init ==
    /\ proposed = {}
    /\ cBal = 0
    /\ cVal = None
    /\ aBal = [a \in Acceptors |-> -1]
    /\ aVBal = [a \in Acceptors |-> -1]
    /\ aVal = [a \in Acceptors |-> None]
    /\ sentMsgs = {}
    /\ learned = {}

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E b \in Ballots : Phase1a(b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E b \in Ballots : Phase2aClassic(b)
    \/ \E b \in Ballots : Phase2aFast(b)
    \/ \E a \in Acceptors : Phase2bClassic(a)
    \/ \E a \in Acceptors : \E v \in Values : Phase2bFast(a, v)
    \/ \E b \in Ballots : CoordinatorRecovery(b)
    \/ Learn

\* Fairness: Weak fairness on all actions
Fairness ==
    /\ \A v \in Values : WF_vars(Propose(v))
    /\ \A b \in Ballots : WF_vars(Phase1a(b))
    /\ \A a \in Acceptors : WF_vars(Phase1b(a))
    /\ \A b \in Ballots : WF_vars(Phase2aClassic(b))
    /\ \A b \in Ballots : WF_vars(Phase2aFast(b))
    /\ \A a \in Acceptors : WF_vars(Phase2bClassic(a))
    /\ \A a \in Acceptors : \A v \in Values : WF_vars(Phase2bFast(a, v))
    /\ WF_vars(Learn)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Agreement - at most one value is learned
Agreement ==
    \A v1, v2 \in learned : v1 = v2

\* Safety: Non-triviality - only proposed values can be learned
NonTriviality ==
    learned \subseteq proposed

\* Safety: Consistency of acceptor votes
VoteConsistency ==
    \A a \in Acceptors :
        aVal[a] # None => aVBal[a] >= 0

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ Agreement
    /\ NonTriviality
    /\ VoteConsistency

\* Liveness: If a value is proposed and the system is fair, eventually some value is learned
Liveness ==
    (proposed # {}) ~> (learned # {})

================================================================================
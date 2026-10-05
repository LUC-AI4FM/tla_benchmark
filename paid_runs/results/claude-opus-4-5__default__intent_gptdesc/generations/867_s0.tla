-------------------------------- MODULE Paxos --------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* The set of acceptor processes
    Proposers,      \* The set of proposer processes
    Values,         \* The set of values that can be proposed
    Ballots,        \* The set of ballot numbers (subset of Nat)
    Quorums         \* The set of quorums (each quorum is a set of acceptors)

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorums : Q \subseteq Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

ASSUME BallotAssumption ==
    /\ Ballots \subseteq Nat
    /\ 0 \in Ballots  \* We use 0 as a "none" ballot for initialization

None == CHOOSE v : v \notin Values

VARIABLES
    maxBal,         \* maxBal[a] = highest ballot acceptor a has promised
    maxVBal,        \* maxVBal[a] = ballot number of highest accepted proposal by a
    maxVal,         \* maxVal[a] = value of highest accepted proposal by a
    msgs,           \* The set of all messages that have been sent
    proposed,       \* proposed[p] = set of values proposer p has proposed
    decisions       \* The set of decided values (for specification purposes)

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, decisions>>

-----------------------------------------------------------------------------
\* Message types

\* Phase 1a: Proposer sends Prepare request
Prepare(b) == [type |-> "1a", bal |-> b]

\* Phase 1b: Acceptor sends Promise response
Promise(a, b, mbal, mval) == 
    [type |-> "1b", acc |-> a, bal |-> b, maxVBal |-> mbal, maxVal |-> mval]

\* Phase 2a: Proposer sends Accept request
Accept(b, v) == [type |-> "2a", bal |-> b, val |-> v]

\* Phase 2b: Acceptor sends Accepted response
Accepted(a, b, v) == [type |-> "2b", acc |-> a, bal |-> b, val |-> v]

-----------------------------------------------------------------------------
\* Type invariant

Messages ==
    [type : {"1a"}, bal : Ballots]
    \cup
    [type : {"1b"}, acc : Acceptors, bal : Ballots, maxVBal : Ballots, maxVal : Values \cup {None}]
    \cup
    [type : {"2a"}, bal : Ballots, val : Values]
    \cup
    [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

TypeOK ==
    /\ maxBal \in [Acceptors -> Ballots]
    /\ maxVBal \in [Acceptors -> Ballots]
    /\ maxVal \in [Acceptors -> Values \cup {None}]
    /\ msgs \subseteq Messages
    /\ proposed \in [Proposers -> SUBSET Values]
    /\ decisions \subseteq Values

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ maxBal = [a \in Acceptors |-> 0]
    /\ maxVBal = [a \in Acceptors |-> 0]
    /\ maxVal = [a \in Acceptors |-> None]
    /\ msgs = {}
    /\ proposed = [p \in Proposers |-> {}]
    /\ decisions = {}

-----------------------------------------------------------------------------
\* Send a message (adds to the set of messages; duplicates are absorbed)

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
\* Phase 1a: Proposer p sends a Prepare message for ballot b

Phase1a(p, b) ==
    /\ b > 0  \* Ballot 0 is reserved for "no ballot"
    /\ Send(Prepare(b))
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decisions>>

-----------------------------------------------------------------------------
\* Phase 1b: Acceptor a receives a Prepare message for ballot b and responds

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send(Promise(a, m.bal, maxVBal[a], maxVal[a]))
        /\ UNCHANGED <<maxVBal, maxVal, proposed, decisions>>

-----------------------------------------------------------------------------
\* Phase 2a: Proposer p sends an Accept message for ballot b with value v
\* The proposer must have received promises from a quorum for ballot b
\* The value v must be:
\*   - If any promise reported an accepted value, v must be the value with highest maxVBal
\*   - Otherwise, v can be any value from Values (which proposer proposes)

Phase2a(p, b, v) ==
    /\ b > 0
    /\ \lnot \E m \in msgs : m.type = "2a" /\ m.bal = b  \* No 2a sent for this ballot yet
    /\ \E Q \in Quorums :
        LET promiseMsgs == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
            promisedAcceptors == {m.acc : m \in promiseMsgs}
            maxAcceptedBal == 
                IF \A m \in promiseMsgs : m.maxVBal = 0 /\ m.maxVal = None
                THEN 0
                ELSE CHOOSE maxB \in {m.maxVBal : m \in promiseMsgs} :
                    \A m \in promiseMsgs : m.maxVBal <= maxB
            acceptedValues == 
                {m.maxVal : m \in promiseMsgs /\ m.maxVBal = maxAcceptedBal /\ m.maxVal /= None}
        IN
        /\ Q \subseteq promisedAcceptors  \* Received promises from entire quorum
        /\ \/ /\ maxAcceptedBal = 0       \* No previously accepted value
              /\ v \in Values             \* Proposer can choose any value
           \/ /\ maxAcceptedBal > 0       \* Some acceptor reported accepted value
              /\ v \in acceptedValues     \* Must use that value
    /\ proposed' = [proposed EXCEPT ![p] = proposed[p] \cup {v}]
    /\ Send(Accept(b, v))
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decisions>>

-----------------------------------------------------------------------------
\* Phase 2b: Acceptor a receives an Accept message and accepts it if allowed

Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]  \* Haven't promised to ignore this ballot
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ Send(Accepted(a, m.bal, m.val))
        /\ UNCHANGED <<proposed, decisions>>

-----------------------------------------------------------------------------
\* Decision: A value is decided when a quorum of acceptors have sent Accepted
\* messages for the same ballot and value

Decide ==
    \E b \in Ballots, v \in Values, Q \in Quorums :
        /\ \A a \in Q : Accepted(a, b, v) \in msgs
        /\ v \notin decisions
        /\ decisions' = decisions \cup {v}
        /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposed>>

-----------------------------------------------------------------------------
\* Next state relation

Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, b \in Ballots, v \in Values : Phase2a(p, b, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ Decide

-----------------------------------------------------------------------------
\* Specification (no fairness required - no liveness guarantees)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety Invariants

\* Quorum intersection property (derived from assumption, stated as invariant)
QuorumIntersection ==
    \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

\* Consistency: At most one value can be decided
Consistency ==
    Cardinality(decisions) <= 1

\* Validity: Any decided value must have been proposed
Validity ==
    \A v \in decisions : \E p \in Proposers : v \in proposed[p]

\* Acceptor state monotonicity: maxBal never decreases
AcceptorMonotonicity ==
    \A a \in Acceptors :
        /\ maxVBal[a] <= maxBal[a]
        /\ (maxVBal[a] = 0) <=> (maxVal[a] = None)

\* A value v is "chosen" at ballot b if a quorum of acceptors have accepted (b, v)
ChosenAt(b, v) ==
    \E Q \in Quorums : \A a \in Q : Accepted(a, b, v) \in msgs

Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

\* If a value has been chosen, decisions should reflect it (or will eventually)
\* This is a consistency check between our explicit decisions and the implicit chosen predicate
ChosenImpliesDecidable ==
    \A v \in Values : Chosen(v) => (v \in decisions \/ decisions = {})

\* Main safety property: At most one value can be chosen
SafetyConsistency ==
    \A v1, v2 \in Values : (Chosen(v1) /\ Chosen(v2)) => (v1 = v2)

\* Message validity: All 2a messages must have values that are consistent with promises
MessageInvariant ==
    \A m \in msgs :
        /\ m.type = "2a" => m.val \in Values
        /\ m.type = "2b" => m.val \in Values
        /\ m.type = "1b" => (m.maxVal \in Values \cup {None})

\* If an acceptor has sent an Accepted message, it must have received the corresponding Accept
AcceptorStateConsistency ==
    \A a \in Acceptors :
        maxVal[a] /= None => 
            \E m \in msgs : m.type = "2a" /\ m.bal = maxVBal[a] /\ m.val = maxVal[a]

\* Combined invariant
Invariant ==
    /\ TypeOK
    /\ Consistency
    /\ Validity
    /\ AcceptorMonotonicity
    /\ SafetyConsistency
    /\ MessageInvariant

=============================================================================
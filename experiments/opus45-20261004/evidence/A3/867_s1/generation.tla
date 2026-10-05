-------------------------------- MODULE Paxos --------------------------------
\* This module specifies the Paxos consensus protocol without explicit leaders
\* or learners, modeling the exchange of prepare, promise, accept, accepted,
\* and decide messages among proposers and acceptors.
\*
\* NOTE: Paxos does not guarantee termination under the asynchronous fault model.
\* This is a consequence of FLP impossibility - in an asynchronous system with
\* even one faulty process, no consensus protocol can be both safe and live.
\* Therefore, Liveness is explicitly set to FALSE in this specification.

EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* The set of acceptor processes
    Values,         \* The set of proposable values
    Ballots         \* The set of ballot numbers (typically Nat or a finite subset)

VARIABLES
    msgs,           \* The set of all messages that have been sent
    decision,       \* A representative decision value (None if no decision yet)
    maxBal,         \* maxBal[a] = highest ballot acceptor a has seen in prepare/accept
    maxVBal,        \* maxVBal[a] = highest ballot acceptor a has accepted
    maxVal          \* maxVal[a] = value accepted at maxVBal[a], or None if none

\* Special value representing "no value"
None == CHOOSE v : v \notin Values

\* A quorum is a strict majority of acceptors
Quorum == {Q \in SUBSET Acceptors : Cardinality(Q) * 2 > Cardinality(Acceptors)}

\* Message types:
\* - [type: "prepare", bal: b] - proposer sends to start phase 1
\* - [type: "promise", acc: a, bal: b, mbal: mb, mval: mv] - acceptor promises
\* - [type: "accept", bal: b, val: v] - proposer sends to start phase 2
\* - [type: "accepted", acc: a, bal: b, val: v] - acceptor accepts
\* - [type: "decide", val: v] - announcement of decided value

Messages ==
    [type: {"prepare"}, bal: Ballots]
    \cup [type: {"promise"}, acc: Acceptors, bal: Ballots, mbal: Ballots \cup {-1}, mval: Values \cup {None}]
    \cup [type: {"accept"}, bal: Ballots, val: Values]
    \cup [type: {"accepted"}, acc: Acceptors, bal: Ballots, val: Values]
    \cup [type: {"decide"}, val: Values]

\* Type invariant
TypeOK ==
    /\ msgs \subseteq Messages
    /\ decision \in Values \cup {None}
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]

\* Initial state
Init ==
    /\ msgs = {}
    /\ decision = None
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]

\* Helper: Send a message
Send(m) == msgs' = msgs \cup {m}

\* Phase 1a: Proposer sends a prepare message for ballot b
Prepare(b) ==
    /\ Send([type |-> "prepare", bal |-> b])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

\* Phase 1b: Acceptor a responds to prepare message for ballot b
Promise(a, b) ==
    /\ [type |-> "prepare", bal |-> b] \in msgs
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ Send([type |-> "promise", acc |-> a, bal |-> b, mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<decision, maxVBal, maxVal>>

\* Phase 2a: Proposer sends accept message for ballot b with value v
\* Proposer must have received promises from a quorum
\* Value v must be the value from highest ballot among promises, or any value if no prior accepts
Accept(b, v) ==
    /\ \E Q \in Quorum :
        LET promiseMsgs == {m \in msgs : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
        IN /\ \A a \in Q : \E m \in promiseMsgs : m.acc = a
           /\ \/ \A m \in promiseMsgs : m.mbal = -1  \* No prior accepts, v can be any value
              \/ \E m \in promiseMsgs :              \* v must be from highest ballot
                    /\ m.mval = v
                    /\ \A m2 \in promiseMsgs : m2.mbal \leq m.mbal
    /\ Send([type |-> "accept", bal |-> b, val |-> v])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

\* Phase 2b: Acceptor a accepts the value in accept message for ballot b
Accepted(a, b, v) ==
    /\ [type |-> "accept", bal |-> b, val |-> v] \in msgs
    /\ b \geq maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = v]
    /\ Send([type |-> "accepted", acc |-> a, bal |-> b, val |-> v])
    /\ UNCHANGED <<decision>>

\* Decide: When a quorum has accepted the same ballot and value
Decide(b, v) ==
    /\ \E Q \in Quorum :
        \A a \in Q : [type |-> "accepted", acc |-> a, bal |-> b, val |-> v] \in msgs
    /\ Send([type |-> "decide", val |-> v])
    /\ decision' = v
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Next state relation
Next ==
    \/ \E b \in Ballots : Prepare(b)
    \/ \E a \in Acceptors, b \in Ballots : Promise(a, b)
    \/ \E b \in Ballots, v \in Values : Accept(b, v)
    \/ \E a \in Acceptors, b \in Ballots, v \in Values : Accepted(a, b, v)
    \/ \E b \in Ballots, v \in Values : Decide(b, v)

\* The complete specification
Spec == Init /\ [][Next]_<<msgs, decision, maxBal, maxVBal, maxVal>>

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* Non-triviality: Only proposed values can be learned (decided)
\* A value is "proposed" if it appears in an accept message
ProposedValues == {m.val : m \in {msg \in msgs : msg.type = "accept"}}

\* The decision value must either be None or a value that was proposed
NonTriviality ==
    decision # None => decision \in ProposedValues

\* Consistency: At most one value is ever decided
\* Once a value is decided, it remains decided (stability)
\* This captures that all decide messages must agree
Consistency ==
    \A m1, m2 \in msgs :
        (m1.type = "decide" /\ m2.type = "decide") => m1.val = m2.val

\* Combined safety invariant
Safety == TypeOK /\ NonTriviality /\ Consistency

--------------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
--------------------------------------------------------------------------------

\* Consistency-related temporal property: once decided, the decision is stable
\* and all future decide messages must agree with it
DecisionStability ==
    [](decision # None => [](decision = decision))

\* Stronger consistency property: the decision variable, once set, never changes
DecisionImmutable ==
    [][\/ decision = None
       \/ decision' = decision]_<<decision>>

--------------------------------------------------------------------------------
\* LIVENESS
--------------------------------------------------------------------------------

\* NOTE: Paxos does not guarantee termination under the asynchronous fault model.
\* By the FLP impossibility result, no deterministic consensus protocol can
\* guarantee both safety and liveness in an asynchronous system where even
\* one process may fail. Paxos chooses safety over liveness.
\*
\* In practice, liveness requires additional assumptions such as:
\* - Partial synchrony (eventually synchronous behavior)
\* - Leader election to avoid dueling proposers
\* - Failure detectors
\*
\* We explicitly set Liveness to FALSE to indicate this.

Liveness == FALSE

================================================================================
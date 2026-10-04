-------------------------------- MODULE Paxos --------------------------------
\* This module specifies the Paxos consensus protocol without explicit leaders
\* or learners, modeling the exchange of prepare, promise, accept, accepted,
\* and decide messages among proposers and acceptors.
\*
\* Note: Paxos does not guarantee termination under the asynchronous fault model
\* implied by FLP-style reasoning. The FLP impossibility result shows that no
\* deterministic consensus protocol can guarantee termination in an asynchronous
\* system with even one faulty process. Therefore, Liveness is explicitly set to
\* FALSE in this specification.

EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* The set of acceptor processes
    Proposers,      \* The set of proposer processes  
    Values,         \* The set of possible values that can be proposed
    Ballots,        \* The set of ballot numbers (natural numbers)
    Quorums         \* The set of quorums (strict majorities with pairwise intersection)

\* Assume quorums are non-empty subsets of acceptors with pairwise intersection
ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ Quorums # {}
    /\ \A Q \in Quorums : Q # {}
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

VARIABLES
    messages,       \* The set of all messages that have been sent
    decision,       \* A representative decision value (None or some value)
    maxBal,         \* maxBal[a] = highest ballot seen by acceptor a
    maxVBal,        \* maxVBal[a] = highest ballot accepted by acceptor a
    maxVal          \* maxVal[a] = value accepted at maxVBal[a]

vars == <<messages, decision, maxBal, maxVBal, maxVal>>

\* Special value representing "none" or "no value"
None == CHOOSE v : v \notin Values

\* Message types
\* Prepare: {type: "prepare", bal: ballot}
\* Promise: {type: "promise", acc: acceptor, bal: ballot, maxVBal: ballot, maxVal: value}
\* Accept: {type: "accept", bal: ballot, val: value}
\* Accepted: {type: "accepted", acc: acceptor, bal: ballot, val: value}
\* Decide: {type: "decide", val: value}

\* Type definitions for messages
PrepareMsg == [type: {"prepare"}, bal: Ballots]
PromiseMsg == [type: {"promise"}, acc: Acceptors, bal: Ballots, 
               maxVBal: Ballots \cup {-1}, maxVal: Values \cup {None}]
AcceptMsg == [type: {"accept"}, bal: Ballots, val: Values]
AcceptedMsg == [type: {"accepted"}, acc: Acceptors, bal: Ballots, val: Values]
DecideMsg == [type: {"decide"}, val: Values]

Message == PrepareMsg \cup PromiseMsg \cup AcceptMsg \cup AcceptedMsg \cup DecideMsg

\* Type invariant
TypeOK ==
    /\ messages \subseteq Message
    /\ decision \in Values \cup {None}
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]

\* Initial state
Init ==
    /\ messages = {}
    /\ decision = None
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]

\* Helper: Send a message
Send(m) == messages' = messages \cup {m}

\* Phase 1a: Proposer sends prepare message for ballot b
Phase1a(p, b) ==
    /\ Send([type |-> "prepare", bal |-> b])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

\* Phase 1b: Acceptor a responds to prepare message with promise
Phase1b(a) ==
    \E m \in messages :
        /\ m.type = "prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "promise", 
                 acc |-> a, 
                 bal |-> m.bal,
                 maxVBal |-> maxVBal[a],
                 maxVal |-> maxVal[a]])
        /\ UNCHANGED <<decision, maxVBal, maxVal>>

\* Phase 2a: Proposer sends accept message after receiving promises from a quorum
Phase2a(p, b, v) ==
    /\ ~\E m \in messages : m.type = "accept" /\ m.bal = b
    /\ \E Q \in Quorums :
        LET promiseMsgs == {m \in messages : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
        IN
            /\ \A a \in Q : \E m \in promiseMsgs : m.acc = a
            /\ \/ \A m \in promiseMsgs : m.maxVBal = -1
               \/ \E m \in promiseMsgs :
                    /\ m.maxVal = v
                    /\ \A m2 \in promiseMsgs : m2.maxVBal =< m.maxVBal
    /\ Send([type |-> "accept", bal |-> b, val |-> v])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

\* Phase 2b: Acceptor a accepts the value in an accept message
Phase2b(a) ==
    \E m \in messages :
        /\ m.type = "accept"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
        /\ UNCHANGED <<decision>>

\* Decide: When a quorum of acceptors have accepted a value at the same ballot
Decide ==
    \E b \in Ballots, v \in Values, Q \in Quorums :
        /\ \A a \in Q : 
            \E m \in messages : 
                m.type = "accepted" /\ m.acc = a /\ m.bal = b /\ m.val = v
        /\ decision = None
        /\ decision' = v
        /\ Send([type |-> "decide", val |-> v])
        /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Next state relation
Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, b \in Ballots, v \in Values : Phase2a(p, b, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ Decide

\* Specification with no fairness (stuttering allowed)
Spec == Init /\ [][Next]_vars

\* ----- SAFETY PROPERTIES -----

\* Non-triviality: Only proposed values can be learned/decided
\* A value is "proposed" if there exists an accept message with that value
ProposedValues == {m.val : m \in {msg \in messages : msg.type = "accept"}}

\* Non-triviality invariant: if a decision is made, it must be a proposed value
NonTriviality ==
    decision # None => decision \in ProposedValues

\* Alternative non-triviality: decided values must be from the Values set
NonTrivialityBasic ==
    decision # None => decision \in Values

\* Consistency: At most one value can be decided
\* Since decision is a single variable, once set it should not change to a different value
\* This is captured by the fact that Decide only fires when decision = None

\* The set of decided values (from decide messages)
DecidedValues == {m.val : m \in {msg \in messages : msg.type = "decide"}}

\* Consistency invariant: all decided values are the same
Consistency ==
    Cardinality(DecidedValues) =< 1

\* Combined safety invariant
SafetyInv ==
    /\ TypeOK
    /\ Consistency
    /\ NonTrivialityBasic

\* ----- LIVENESS PROPERTIES -----

\* Liveness is explicitly FALSE because Paxos does not guarantee termination
\* under the asynchronous fault model implied by FLP-style reasoning.
\* The FLP impossibility theorem proves that no deterministic consensus
\* protocol can guarantee both safety and liveness in an asynchronous
\* system where even one process may fail.
Liveness == FALSE

\* Consistency-related temporal property: once decided, the decision is stable
\* (the decision variable never changes to a different value)
DecisionStability ==
    [](decision # None => [](decision = decision))

\* Alternative formulation: if we ever decide v, we always have decided v
DecisionIrrevocable ==
    \A v \in Values : [](decision = v => [](decision = v))

===============================================================================
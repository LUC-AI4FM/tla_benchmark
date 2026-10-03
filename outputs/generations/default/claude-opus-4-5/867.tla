-------------------------------- MODULE Paxos --------------------------------
\* This module specifies the Paxos consensus protocol without explicit leaders
\* or learners, modeling the exchange of prepare, promise, accept, accepted,
\* and decide messages among proposers and acceptors.
\*
\* Note: Paxos does not guarantee termination under the asynchronous fault model
\* implied by FLP-style reasoning. The Fischer-Lynch-Paterson impossibility result
\* shows that no deterministic consensus protocol can guarantee termination in an
\* asynchronous system with even one faulty process. Therefore, liveness is
\* explicitly set to FALSE in this specification.

EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* The set of all acceptors
    Proposers,      \* The set of all proposers  
    Values,         \* The set of possible values that can be proposed
    Ballots,        \* The set of ballot numbers (typically natural numbers)
    Quorums         \* The set of quorums (strict majorities with pairwise intersection)

\* Assume quorums are subsets of acceptors with pairwise intersection property
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorums : Q \subseteq Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

\* Special value representing "none" or "null"
None == CHOOSE v : v \notin Values

VARIABLES
    messages,       \* The set of all sent messages
    decision,       \* A representative decision value (None if no decision yet)
    maxBal,         \* maxBal[a] = highest ballot seen by acceptor a
    maxVBal,        \* maxVBal[a] = highest ballot accepted by acceptor a
    maxVal          \* maxVal[a] = value accepted at maxVBal[a]

vars == <<messages, decision, maxBal, maxVBal, maxVal>>

\* Message types:
\* - [type |-> "prepare", bal |-> b, prop |-> p]
\* - [type |-> "promise", bal |-> b, acc |-> a, maxVBal |-> vb, maxVal |-> v]
\* - [type |-> "accept", bal |-> b, val |-> v, prop |-> p]
\* - [type |-> "accepted", bal |-> b, val |-> v, acc |-> a]
\* - [type |-> "decide", val |-> v]

TypeOK ==
    /\ messages \subseteq (
        [type : {"prepare"}, bal : Ballots, prop : Proposers] \cup
        [type : {"promise"}, bal : Ballots, acc : Acceptors, maxVBal : Ballots \cup {-1}, maxVal : Values \cup {None}] \cup
        [type : {"accept"}, bal : Ballots, val : Values, prop : Proposers] \cup
        [type : {"accepted"}, bal : Ballots, val : Values, acc : Acceptors] \cup
        [type : {"decide"}, val : Values]
       )
    /\ decision \in Values \cup {None}
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]

\* Helper: Send a message
Send(m) == messages' = messages \cup {m}

\* Initial state
Init ==
    /\ messages = {}
    /\ decision = None
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]

\* Phase 1a: Proposer sends prepare request with ballot b
Prepare(p, b) ==
    /\ Send([type |-> "prepare", bal |-> b, prop |-> p])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

\* Phase 1b: Acceptor responds to prepare request with promise
Promise(a, b) ==
    /\ \E m \in messages :
        /\ m.type = "prepare"
        /\ m.bal = b
        /\ b > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = b]
        /\ Send([type |-> "promise", 
                 bal |-> b, 
                 acc |-> a, 
                 maxVBal |-> maxVBal[a], 
                 maxVal |-> maxVal[a]])
        /\ UNCHANGED <<decision, maxVBal, maxVal>>

\* Phase 2a: Proposer sends accept request after receiving promises from a quorum
Accept(p, b, v) ==
    /\ \E Q \in Quorums :
        LET promises == {m \in messages : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
        IN
            /\ \A a \in Q : \E m \in promises : m.acc = a
            \* Choose value: if any promise has an accepted value, use the one with highest ballot
            /\ LET validPromises == {m \in promises : m.maxVBal >= 0}
               IN
                  \/ /\ validPromises = {}
                     /\ v \in Values  \* Proposer can choose any value
                  \/ /\ validPromises /= {}
                     /\ \E m \in validPromises :
                        /\ m.maxVal = v
                        /\ \A m2 \in validPromises : m.maxVBal >= m2.maxVBal
    /\ Send([type |-> "accept", bal |-> b, val |-> v, prop |-> p])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

\* Phase 2b: Acceptor accepts proposal
Accepted(a, b, v) ==
    /\ \E m \in messages :
        /\ m.type = "accept"
        /\ m.bal = b
        /\ m.val = v
        /\ b >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = b]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
        /\ maxVal' = [maxVal EXCEPT ![a] = v]
        /\ Send([type |-> "accepted", bal |-> b, val |-> v, acc |-> a])
        /\ UNCHANGED decision

\* Decide: When a quorum has accepted the same ballot/value, decide on that value
Decide(v) ==
    /\ decision = None
    /\ \E b \in Ballots, Q \in Quorums :
        \A a \in Q : \E m \in messages :
            /\ m.type = "accepted"
            /\ m.bal = b
            /\ m.val = v
            /\ m.acc = a
    /\ decision' = v
    /\ Send([type |-> "decide", val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Next state relation
Next ==
    \/ \E p \in Proposers, b \in Ballots : Prepare(p, b)
    \/ \E a \in Acceptors, b \in Ballots : Promise(a, b)
    \/ \E p \in Proposers, b \in Ballots, v \in Values : Accept(p, b, v)
    \/ \E a \in Acceptors, b \in Ballots, v \in Values : Accepted(a, b, v)
    \/ \E v \in Values : Decide(v)

\* Specification
Spec == Init /\ [][Next]_vars

\* =============================================================================
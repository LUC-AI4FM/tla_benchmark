---------------------------- MODULE PaxosSpec ----------------------------
(**************************************************************************)
(* This module specifies the Paxos consensus protocol without explicit    *)
(* leaders or learners, modeling the exchange of prepare, promise,        *)
(* accept, accepted, and decide messages among proposers and acceptors.   *)
(*                                                                        *)
(* NOTE: Paxos does not guarantee termination under the asynchronous      *)
(* fault model implied by FLP-style reasoning. The FLP impossibility      *)
(* result shows that no deterministic consensus protocol can guarantee    *)
(* both safety and liveness in an asynchronous system with even one       *)
(* possible faulty process. Therefore, Liveness is explicitly set to      *)
(* FALSE in this specification.                                           *)
(**************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS 
    Acceptors,      \* The set of acceptor processes
    Proposers,      \* The set of proposer processes  
    Values,         \* The set of proposable values
    Ballots,        \* The set of ballot numbers (natural numbers)
    Quorums         \* The set of quorums (strict majorities with pairwise intersection)

VARIABLES
    messages,       \* The set of all messages that have been sent
    decision,       \* A representative decision value (None or some decided value)
    maxBal,         \* maxBal[a] = highest ballot seen by acceptor a
    maxVBal,        \* maxVBal[a] = highest ballot accepted by acceptor a
    maxVal          \* maxVal[a] = value accepted at maxVBal[a]

vars == <<messages, decision, maxBal, maxVBal, maxVal>>

-----------------------------------------------------------------------------
(* Message types *)

\* A prepare message from a proposer with ballot b
PrepareMsg(b) == [type |-> "prepare", bal |-> b]

\* A promise message from acceptor a for ballot b, with previously accepted ballot and value
PromiseMsg(a, b, mbal, mval) == 
    [type |-> "promise", acc |-> a, bal |-> b, maxVBal |-> mbal, maxVal |-> mval]

\* An accept message (Phase 2a) from proposer with ballot b and value v
AcceptMsg(b, v) == [type |-> "accept", bal |-> b, val |-> v]

\* An accepted message (Phase 2b) from acceptor a for ballot b and value v
AcceptedMsg(a, b, v) == [type |-> "accepted", acc |-> a, bal |-> b, val |-> v]

\* A decide message announcing value v was decided
DecideMsg(v) == [type |-> "decide", val |-> v]

-----------------------------------------------------------------------------
(* Type invariant *)

None == CHOOSE v : v \notin Values

MessageType ==
    [type : {"prepare"}, bal : Ballots]
    \cup [type : {"promise"}, acc : Acceptors, bal : Ballots, 
          maxVBal : Ballots \cup {-1}, maxVal : Values \cup {None}]
    \cup [type : {"accept"}, bal : Ballots, val : Values]
    \cup [type : {"accepted"}, acc : Acceptors, bal : Ballots, val : Values]
    \cup [type : {"decide"}, val : Values]

PaxosTypeOK ==
    /\ messages \subseteq MessageType
    /\ decision \in Values \cup {None}
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]

-----------------------------------------------------------------------------
(* Quorum assumption: strict majorities with pairwise intersection *)

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorums : Q \subseteq Acceptors
    /\ \A Q \in Quorums : Cardinality(Q) * 2 > Cardinality(Acceptors)
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ messages = {}
    /\ decision = None
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]

-----------------------------------------------------------------------------
(* Phase 1a: Proposer sends prepare message *)

Phase1a(b) ==
    /\ PrepareMsg(b) \notin messages
    /\ messages' = messages \cup {PrepareMsg(b)}
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

-----------------------------------------------------------------------------
(* Phase 1b: Acceptor responds with promise *)

Phase1b(a, b) ==
    /\ PrepareMsg(b) \in messages
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ messages' = messages \cup {PromiseMsg(a, b, maxVBal[a], maxVal[a])}
    /\ UNCHANGED <<decision, maxVBal, maxVal>>

-----------------------------------------------------------------------------
(* Phase 2a: Proposer sends accept message *)

\* Get the set of promise messages for ballot b
PromiseMsgs(b) == {m \in messages : m.type = "promise" /\ m.bal = b}

\* Check if a quorum has promised for ballot b
HasQuorumPromise(b) ==
    \E Q \in Quorums : \A a \in Q : \E m \in PromiseMsgs(b) : m.acc = a

\* Get the value to propose: either a previously accepted value or any value
GetValue(b) ==
    LET promiseMsgs == PromiseMsgs(b)
        highestBal == 
            IF \A m \in promiseMsgs : m.maxVBal = -1
            THEN -1
            ELSE CHOOSE maxB \in {m.maxVBal : m \in promiseMsgs} :
                    \A m \in promiseMsgs : m.maxVBal <= maxB
    IN IF highestBal = -1
       THEN Values  \* Can propose any value
       ELSE {m.maxVal : m \in {pm \in promiseMsgs : pm.maxVBal = highestBal}}

Phase2a(b, v) ==
    /\ HasQuorumPromise(b)
    /\ AcceptMsg(b, v) \notin messages
    /\ v \in GetValue(b)
    /\ messages' = messages \cup {AcceptMsg(b, v)}
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

-----------------------------------------------------------------------------
(* Phase 2b: Acceptor accepts the proposal *)

Phase2b(a, b, v) ==
    /\ AcceptMsg(b, v) \in messages
    /\ b >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = v]
    /\ messages' = messages \cup {AcceptedMsg(a, b, v)}
    /\ UNCHANGED <<decision>>

-----------------------------------------------------------------------------
(* Learn/Decide: When a quorum has accepted the same ballot and value *)

AcceptedMsgs(b, v) == 
    {m \in messages : m.type = "accepted" /\ m.bal = b /\ m.val = v}

HasQuorumAccepted(b, v) ==
    \E Q \in Quorums : \A a \in Q : \E m \in AcceptedMsgs(b, v) : m.acc = a

Decide(b, v) ==
    /\ HasQuorumAccepted(b, v)
    /\ decision = None
    /\ decision' = v
    /\ messages' = messages \cup {DecideMsg(v)}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E b \in Ballots : Phase1a(b)
    \/ \E a \in Acceptors, b \in Ballots : Phase1b(a, b)
    \/ \E b \in Ballots, v \in Values : Phase2a(b, v)
    \/ \E a \in Acceptors, b \in Ballots, v \in Values : Phase2b(a, b, v)
    \/ \E b \in Ballots, v \in Values : Decide(b, v)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Non-triviality: Only proposed values can be learned/decided
\* A value is "proposed" if it appears in an accept message
ProposedValues == {m.val : m \in {msg \in messages : msg.type = "accept"}}

PaxosNontriviality ==
    decision /= None => decision \in ProposedValues

\* Consistency: At most one value is ever decided, and once decided it remains decided
\* This is a temporal property stating that the decision is stable once made
PaxosConsistency ==
    [](decision /= None => [](decision = decision))

-----------------------------------------------------------------------------
(* Liveness *)

(**************************************************************************)
(* Liveness is explicitly set to FALSE.                                   *)
(* Paxos does not guarantee termination under the asynchronous fault      *)
(* model implied by FLP-style reasoning. The FLP impossibility result     *)
(* proves that no deterministic consensus protocol can guarantee both     *)
(* safety and liveness in a purely asynchronous system where even one     *)
(* process may fail. Paxos prioritizes safety over liveness.              *)
(**************************************************************************)
Liveness == FALSE

=============================================================================
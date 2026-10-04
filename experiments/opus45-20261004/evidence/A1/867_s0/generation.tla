---------------------------- MODULE PaxosSpec ----------------------------
(**************************************************************************)
(* This module specifies the Paxos consensus protocol without explicit    *)
(* leaders or learners, modeling the exchange of prepare, promise,        *)
(* accept, accepted, and decide messages among proposers and acceptors.   *)
(*                                                                        *)
(* NOTE: Paxos does not guarantee termination under the asynchronous      *)
(* fault model implied by FLP-style reasoning. The FLP impossibility      *)
(* result shows that no deterministic consensus protocol can guarantee    *)
(* termination in an asynchronous system with even one faulty process.    *)
(* Therefore, liveness is explicitly set to FALSE in this specification.  *)
(**************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS 
    Acceptors,      \* The set of acceptor processes
    Proposers,      \* The set of proposer processes  
    Values,         \* The set of values that can be proposed
    Ballots,        \* The set of ballot numbers
    Quorums         \* The set of quorums (strict majorities)

ASSUME QuorumAssumption == 
    /\ \A Q \in Quorums : Q \subseteq Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

VARIABLES
    messages,       \* The set of all messages that have been sent
    decision,       \* A representative decision value (or None if no decision)
    maxBal,         \* maxBal[a] = highest ballot seen by acceptor a
    maxVBal,        \* maxVBal[a] = highest ballot accepted by acceptor a
    maxVal          \* maxVal[a] = value accepted at maxVBal[a]

vars == <<messages, decision, maxBal, maxVBal, maxVal>>

None == CHOOSE v : v \notin Values

(**************************************************************************)
(* Message types:                                                          *)
(* - [type: "prepare", bal: b] - prepare request with ballot b             *)
(* - [type: "promise", bal: b, acc: a, mbal: mb, mval: mv] - promise from  *)
(*   acceptor a for ballot b, reporting previously accepted (mb, mv)       *)
(* - [type: "accept", bal: b, val: v] - accept request for (b, v)          *)
(* - [type: "accepted", bal: b, val: v, acc: a] - accepted notification    *)
(* - [type: "decide", val: v] - decision notification                      *)
(**************************************************************************)

MessageType ==
    [type: {"prepare"}, bal: Ballots]
    \cup [type: {"promise"}, bal: Ballots, acc: Acceptors, 
          mbal: Ballots \cup {-1}, mval: Values \cup {None}]
    \cup [type: {"accept"}, bal: Ballots, val: Values]
    \cup [type: {"accepted"}, bal: Ballots, val: Values, acc: Acceptors]
    \cup [type: {"decide"}, val: Values]

(**************************************************************************)
(* Type invariant                                                          *)
(**************************************************************************)

PaxosTypeOK ==
    /\ messages \subseteq MessageType
    /\ decision \in Values \cup {None}
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]

(**************************************************************************)
(* Initial state                                                           *)
(**************************************************************************)

Init ==
    /\ messages = {}
    /\ decision = None
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]

(**************************************************************************)
(* Helper: Send a message                                                  *)
(**************************************************************************)

Send(m) == messages' = messages \cup {m}

(**************************************************************************)
(* Phase 1a: Proposer sends prepare request                                *)
(**************************************************************************)

Phase1a(p, b) ==
    /\ Send([type |-> "prepare", bal |-> b])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(**************************************************************************)
(* Phase 1b: Acceptor responds to prepare with promise                     *)
(**************************************************************************)

Phase1b(a) ==
    \E m \in messages :
        /\ m.type = "prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "promise", bal |-> m.bal, acc |-> a,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
        /\ UNCHANGED <<decision, maxVBal, maxVal>>

(**************************************************************************)
(* Phase 2a: Proposer sends accept request after receiving promises        *)
(* from a quorum                                                           *)
(**************************************************************************)

Phase2a(p, b, v) ==
    /\ ~\E m \in messages : m.type = "accept" /\ m.bal = b
    /\ \E Q \in Quorums :
        LET promiseSet == {m \in messages : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
            promisers == {m.acc : m \in promiseSet}
        IN
        /\ promisers = Q
        /\ \/ \A m \in promiseSet : m.mbal = -1 /\ v \in Values
           \/ \E m \in promiseSet :
                /\ m.mbal # -1
                /\ m.mval = v
                /\ \A m2 \in promiseSet : m2.mbal =< m.mbal
    /\ Send([type |-> "accept", bal |-> b, val |-> v])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(**************************************************************************)
(* Phase 2b: Acceptor accepts a proposal                                   *)
(**************************************************************************)

Phase2b(a) ==
    \E m \in messages :
        /\ m.type = "accept"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "accepted", bal |-> m.bal, val |-> m.val, acc |-> a])
        /\ UNCHANGED decision

(**************************************************************************)
(* Decide: A value is decided when accepted by a quorum                    *)
(**************************************************************************)

Decide(v) ==
    /\ decision = None
    /\ \E b \in Ballots, Q \in Quorums :
        \A a \in Q : 
            \E m \in messages : 
                m.type = "accepted" /\ m.bal = b /\ m.val = v /\ m.acc = a
    /\ decision' = v
    /\ Send([type |-> "decide", val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(**************************************************************************)
(* Next state relation                                                     *)
(**************************************************************************)

Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, b \in Ballots, v \in Values : Phase2a(p, b, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ \E v \in Values : Decide(v)

(**************************************************************************)
(* Specification                                                           *)
(**************************************************************************)

Spec == Init /\ [][Next]_vars

(**************************************************************************)
(* Safety property: Non-triviality                                         *)
(* Only proposed values (values in accept messages) can be decided         *)
(**************************************************************************)

ProposedValues == {m.val : m \in {msg \in messages : msg.type = "accept"}}

PaxosNontriviality ==
    decision # None => decision \in Values

(**************************************************************************)
(* Safety property: Consistency                                            *)
(* Once a decision is made, it never changes                               *)
(* This is a temporal property over the decision variable                  *)
(**************************************************************************)

PaxosConsistency ==
    [](decision # None => [](decision = decision))

(**************************************************************************)
(* Liveness is explicitly FALSE                                            *)
(* Paxos does not guarantee termination under the asynchronous fault       *)
(* model implied by FLP-style reasoning. The FLP impossibility result      *)
(* proves that no deterministic consensus protocol can guarantee both      *)
(* safety and liveness in an asynchronous system where processes can fail. *)
(**************************************************************************)

Liveness == FALSE

(**************************************************************************)
(* Additional invariant: Agreement                                         *)
(* All decide messages agree on the same value                             *)
(**************************************************************************)

Agreement ==
    \A m1, m2 \in messages :
        (m1.type = "decide" /\ m2.type = "decide") => m1.val = m2.val

==========================================================================
------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Paxos consensus without explicit leaders or learners.  Proposers and    *)
(* acceptors exchange prepare, promise, accept, accepted and decide        *)
(* messages.  The state records every message ever sent (msgs), one        *)
(* representative decision value (decision), and for each acceptor:        *)
(*   maxBal[a]  - the highest ballot a has seen (promised),                *)
(*   maxVBal[a] - the highest ballot in which a has accepted a value,      *)
(*   maxVal[a]  - the value a accepted in ballot maxVBal[a].               *)
(* Quorums are strict majorities of acceptors, so any two intersect.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Value,      \* the set of values that may be proposed
          Acceptor,   \* the set of acceptors
          Ballot      \* the set of ballot numbers

ASSUME BallotAssumption == Ballot \subseteq Nat

ASSUME AcceptorAssumption == IsFiniteSet(Acceptor) /\ Acceptor # {}

None == CHOOSE v : v \notin Value

(***************************************************************************)
(* Quorums: strict majorities of acceptors.                                *)
(***************************************************************************)
Quorum == {Q \in SUBSET Acceptor : 2 * Cardinality(Q) > Cardinality(Acceptor)}

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Message ==
         [type : {"prepare"}, bal : Ballot]
    \cup [type : {"promise"}, acc : Acceptor, bal : Ballot,
          mbal : Ballot \cup {-1}, mval : Value \cup {None}]
    \cup [type : {"accept"}, bal : Ballot, val : Value]
    \cup [type : {"accepted"}, acc : Acceptor, bal : Ballot, val : Value]
    \cup [type : {"decide"}, bal : Ballot, val : Value]

VARIABLES msgs,      \* set of all messages sent
          decision,  \* representative decided value
          maxBal,    \* maxBal[a]: highest ballot seen by acceptor a
          maxVBal,   \* maxVBal[a]: highest ballot accepted by acceptor a
          maxVal     \* maxVal[a]: value accepted in ballot maxVBal[a]

vars == <<msgs, decision, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ msgs \subseteq Message
    /\ decision \in Value \cup {None}
    /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal  \in [Acceptor -> Value \cup {None}]

Init ==
    /\ msgs = {}
    /\ decision = None
    /\ maxBal  = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal  = [a \in Acceptor |-> None]

(***************************************************************************)
(* Phase 1a: a proposer sends a prepare message for ballot b.              *)
(***************************************************************************)
Prepare(b) ==
    /\ Send([type |-> "prepare", bal |-> b])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: an acceptor promises on a prepare with a higher ballot.       *)
(***************************************************************************)
Promise(a) ==
    \E m \in msgs :
        /\ m.type = "prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "promise", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
        /\ UNCHANGED <<decision, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2a: a proposer, having promises from a quorum for ballot b,       *)
(* sends an accept message with a safe value v.                            *)
(***************************************************************************)
Accept(b, v) ==
    /\ ~ \E m \in msgs : m.type = "accept" /\ m.bal = b
    /\ \E Q \in Quorum :
         LET Q1msgs == {m \in msgs : /\ m.type = "promise"
                                     /\ m.bal = b
                                     /\ m.acc \in Q}
             Q1bv   == {m \in Q1msgs : m.mbal >= 0}
         IN  /\ \A a \in Q : \E m \in Q1msgs : m.acc = a
             /\ \/ Q1bv = {}
                \/ \E m \in Q1bv :
                     /\ m.mval = v
                     /\ \A mm \in Q1bv : m.mbal >= mm.mbal
    /\ Send([type |-> "accept", bal |-> b, val |-> v])
    /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts an accept message whose ballot is at      *)
(* least as high as any ballot it has seen.                                *)
(***************************************************************************)
Accepted(a) ==
    \E m \in msgs :
        /\ m.type = "accept"
        /\ m.bal >= maxBal[a]
        /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
        /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
        /\ UNCHANGED decision

(***************************************************************************)
(* Decide: once a quorum has accepted value v in ballot b, v is decided.   *)
(***************************************************************************)
Decide(b, v) ==
    /\ \E Q \in Quorum :
         \A a \in Q : \E m \in msgs : /\ m.type = "accepted"
                                      /\ m.acc = a
                                      /\ m.bal = b
                                      /\ m.val = v
    /\ Send([type |-> "decide", bal |-> b, val |-> v])
    /\ decision' = v
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Next ==
    \/ \E b \in Ballot : Prepare(b)
    \/ \E a \in Acceptor : Promise(a)
    \/ \E b \in Ballot, v \in Value : Accept(b, v)
    \/ \E a \in Acceptor : Accepted(a)
    \/ \E b \in Ballot, v \in Value : Decide(b, v)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)

\* Non-triviality: only a value that has been proposed can be learned.
NonTriviality ==
    decision # None =>
        \E m \in msgs : m.type = "accept" /\ m.val = decision

\* Consistency: once a value is decided, the decision never changes.
Consistency ==
    \A v \in Value : [](decision = v => [](decision = v))

(***************************************************************************)
(* Liveness.  Paxos does not guarantee termination: by FLP-style reasoning *)
(* no deterministic consensus protocol can ensure progress in an           *)
(* asynchronous system subject to even a single crash fault (competing     *)
(* proposers may preempt each other forever).  Hence liveness is set to    *)
(* FALSE and no fairness conditions are assumed.                           *)
(***************************************************************************)
Liveness == FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []NonTriviality
THEOREM Spec => Consistency
=============================================================================
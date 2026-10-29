------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Paxos consensus without explicit leaders or learners.  Proposer        *)
(* actions (Prepare, Accept) and learner actions (Decide) can be taken by *)
(* any process.  Messages are never removed from msgs, so loss,           *)
(* duplication and reordering are allowed.                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Value,      \* the set of values that may be proposed
          Acceptor,   \* the set of acceptors
          Quorum      \* the set of quorums (strict majorities)

ASSUME QuorumAssumption ==
          /\ \A Q \in Quorum : Q \subseteq Acceptor
          /\ \A Q \in Quorum : 2 * Cardinality(Q) > Cardinality(Acceptor)
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

None == CHOOSE v : v \notin Value

Message ==
       [type : {"prepare"}, bal : Ballot]
  \cup [type : {"promise"}, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"accept"}, bal : Ballot, val : Value]
  \cup [type : {"accepted"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"decide"}, bal : Ballot, val : Value]

VARIABLES msgs,      \* the set of all messages sent so far
          decision,  \* a representative decided value (None if none)
          maxBal,    \* maxBal[a]: highest ballot seen by acceptor a
          maxVBal,   \* maxVBal[a]: highest ballot in which a accepted
          maxVal     \* maxVal[a]: value a accepted in ballot maxVBal[a]

vars == <<msgs, decision, maxBal, maxVBal, maxVal>>

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

Send(m) == msgs' = msgs \cup {m}

(* Phase 1a: a proposer starts ballot b by sending a prepare message. *)
Prepare(b) ==
  /\ ~ \E m \in msgs : m.type = "prepare" /\ m.bal = b
  /\ Send([type |-> "prepare", bal |-> b])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(* Phase 1b: an acceptor promises not to take part in lower ballots. *)
Promise(a) ==
  \E m \in msgs :
    /\ m.type = "prepare"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "promise", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<decision, maxVBal, maxVal>>

(* Phase 2a: a proposer that received promises from a quorum for ballot b *)
(* asks acceptors to accept a safe value v.                               *)
Accept(b, v) ==
  /\ ~ \E m \in msgs : m.type = "accept" /\ m.bal = b
  /\ \E Q \in Quorum :
       LET Q1b  == {m \in msgs : /\ m.type = "promise"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "accept", bal |-> b, val |-> v])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(* Phase 2b: an acceptor accepts a value unless it promised a higher ballot. *)
Accepted(a) ==
  \E m \in msgs :
    /\ m.type = "accept"
    /\ m.bal >= maxBal[a]
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
    /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED decision

(* Decision: a value accepted by a quorum in the same ballot is decided. *)
Decide(b, v) ==
  /\ \E Q \in Quorum :
       \A a \in Q : [type |-> "accepted", acc |-> a, bal |-> b, val |-> v] \in msgs
  /\ Send([type |-> "decide", bal |-> b, val |-> v])
  /\ decision' = v
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Next ==
  \/ \E b \in Ballot : Prepare(b)
  \/ \E b \in Ballot, v \in Value : Accept(b, v)
  \/ \E b \in Ballot, v \in Value : Decide(b, v)
  \/ \E a \in Acceptor : Promise(a) \/ Accepted(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

(* Non-triviality: only proposed values can be learned. *)
Nontriviality ==
  /\ decision # None =>
       \E m \in msgs : m.type = "accept" /\ m.val = decision
  /\ \A d \in msgs :
       d.type = "decide" =>
         \E m \in msgs : m.type = "accept" /\ m.val = d.val

(* Consistency: once a value is decided, the decision never changes. *)
Consistency ==
  [][decision # None => decision' = decision]_decision

(* Agreement among all decide messages (state-level consistency). *)
Agreement ==
  \A m1, m2 \in msgs :
    (m1.type = "decide" /\ m2.type = "decide") => m1.val = m2.val

-----------------------------------------------------------------------------
(* Liveness *)

(* Paxos does not guarantee termination: by FLP-style reasoning, no      *)
(* deterministic consensus protocol can guarantee that a decision is     *)
(* eventually reached in an asynchronous system subject to failures      *)
(* (e.g., competing proposers can preempt each other forever).  Hence    *)
(* the liveness property is explicitly set to FALSE.                     *)
Liveness == FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []Nontriviality
THEOREM Spec => Consistency
=============================================================================
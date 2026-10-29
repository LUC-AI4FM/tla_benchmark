------------------------------- MODULE PaxosDecide -------------------------------
(***************************************************************************)
(* Paxos consensus without explicit leaders or learners.                   *)
(*                                                                         *)
(* Proposers and acceptors exchange prepare (1a), promise (1b),            *)
(* accept (2a), accepted (2b) and decide messages.  The state holds the    *)
(* set of all messages sent so far, one representative decision value,    *)
(* and for each acceptor:                                                  *)
(*   - maxBal  : the highest ballot it has seen,                           *)
(*   - maxVBal : the highest ballot in which it has accepted a value,      *)
(*   - maxVal  : the value it accepted in ballot maxVBal.                  *)
(* Quorums are strict majorities of acceptors, so any two quorums          *)
(* intersect.                                                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Values,     \* The set of values that may be proposed
          Acceptors,  \* The set of acceptors
          Ballots     \* The set of ballot numbers

ASSUME BallotsAssump == Ballots \subseteq Nat
ASSUME AcceptorsAssump == IsFiniteSet(Acceptors) /\ Acceptors # {}

None == CHOOSE v : v \notin Values

(* Quorums are strict majorities of the acceptors. *)
Quorum == {Q \in SUBSET Acceptors : Cardinality(Q) * 2 > Cardinality(Acceptors)}

(* Any two strict majorities intersect. *)
THEOREM QuorumIntersection == \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Message ==
       [type : {"prepare"}, bal : Ballots]
  \cup [type : {"promise"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"accept"}, bal : Ballots, val : Values]
  \cup [type : {"accepted"}, acc : Acceptors, bal : Ballots, val : Values]
  \cup [type : {"decide"}, bal : Ballots, val : Values]

VARIABLES msgs,      \* The set of all messages that have been sent
          decision,  \* A representative decided value (None if undecided)
          maxBal,    \* maxBal[a]  : highest ballot seen by acceptor a
          maxVBal,   \* maxVBal[a] : highest ballot in which a accepted a value
          maxVal     \* maxVal[a]  : value accepted by a in ballot maxVBal[a]

vars == <<msgs, decision, maxBal, maxVBal, maxVal>>

TypeOK ==
  /\ msgs \subseteq Message
  /\ decision \in Values \cup {None}
  /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal \in [Acceptors -> Values \cup {None}]

Init ==
  /\ msgs = {}
  /\ decision = None
  /\ maxBal = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal = [a \in Acceptors |-> None]

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Phase 1a: a proposer sends a prepare message for ballot b.              *)
(***************************************************************************)
Prepare(b) ==
  /\ Send([type |-> "prepare", bal |-> b])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: acceptor a promises not to participate in lower ballots.      *)
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
(* Phase 2a: a proposer, having promises from a quorum for ballot b,      *)
(* asks acceptors to accept a safe value v in ballot b.                   *)
(***************************************************************************)
Accept(b, v) ==
  /\ ~ \E m \in msgs : m.type = "accept" /\ m.bal = b
  /\ \E Q \in Quorum :
       LET S == {m \in msgs : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
       IN  /\ \A a \in Q : \E m \in S : m.acc = a
           /\ \/ \A m \in S : m.mbal = -1
              \/ \E c \in 0..(b-1) :
                    /\ \A m \in S : m.mbal =< c
                    /\ \E m \in S : m.mbal = c /\ m.mval = v
  /\ Send([type |-> "accept", bal |-> b, val |-> v])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b: acceptor a accepts a value unless it promised a higher ballot.*)
(***************************************************************************)
Accepted(a) ==
  \E m \in msgs :
    /\ m.type = "accept"
    /\ m.bal >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
    /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED decision

(***************************************************************************)
(* Decide: once a quorum has accepted v in ballot b, v is decided.         *)
(***************************************************************************)
Decide(b, v) ==
  /\ \E Q \in Quorum :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "accepted"
          /\ m.acc = a
          /\ m.bal = b
          /\ m.val = v
  /\ Send([type |-> "decide", bal |-> b, val |-> v])
  /\ decision' = v
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Next ==
  \/ \E b \in Ballots : Prepare(b)
  \/ \E a \in Acceptors : Promise(a) \/ Accepted(a)
  \/ \E b \in Ballots, v \in Values : Accept(b, v) \/ Decide(b, v)

(***************************************************************************)
(* No fairness is assumed: Paxos does not guarantee termination.           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* Non-triviality: only proposed values can be learned. *)
Nontriviality ==
  /\ decision # None =>
       \E m \in msgs : m.type = "accept" /\ m.val = decision
  /\ \A d \in msgs :
       d.type = "decide" =>
         \E m \in msgs : m.type = "accept" /\ m.bal = d.bal /\ m.val = d.val

(* Consistency: once a value is decided, the decision never changes. *)
Consistency == [][decision # None => decision' = decision]_decision

(***************************************************************************)
(* Liveness                                                                *)
(*                                                                         *)
(* Paxos does not guarantee termination.  By FLP-style reasoning, no      *)
(* deterministic consensus protocol can guarantee termination in an        *)
(* asynchronous system where even one process may crash: competing         *)
(* proposers can keep preempting each other's ballots forever.  So         *)
(* liveness is set to FALSE.                                               *)
(***************************************************************************)
Liveness == FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []Nontriviality
THEOREM Spec => Consistency
=============================================================================
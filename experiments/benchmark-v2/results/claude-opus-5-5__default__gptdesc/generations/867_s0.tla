------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Paxos consensus without explicit leaders or learners.  Proposers and    *)
(* acceptors exchange prepare, promise, accept, accepted and decide        *)
(* messages.  The state records every message sent, a representative       *)
(* decision value, and for each acceptor:                                  *)
(*   - maxBal  : the highest ballot it has seen,                           *)
(*   - maxVBal : the highest ballot in which it has accepted a value,      *)
(*   - maxVal  : the value it accepted in ballot maxVBal.                  *)
(* Quorums are strict majorities of acceptors, so any two intersect.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Value, Acceptor, MaxBallot

ASSUME /\ Acceptor # {}
       /\ IsFiniteSet(Acceptor)
       /\ MaxBallot \in Nat

Ballot == 0..MaxBallot

None == CHOOSE v : v \notin Value

Quorum == {Q \in SUBSET Acceptor : 2 * Cardinality(Q) > Cardinality(Acceptor)}

THEOREM QuorumAssumption ==
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Message ==
         [type : {"prepare"},  bal : Ballot]
    \cup [type : {"promise"},  acc : Acceptor, bal : Ballot,
          mbal : Ballot \cup {-1}, mval : Value \cup {None}]
    \cup [type : {"accept"},   bal : Ballot, val : Value]
    \cup [type : {"accepted"}, acc : Acceptor, bal : Ballot, val : Value]
    \cup [type : {"decide"},   bal : Ballot, val : Value]

VARIABLES msgs, decision, maxBal, maxVBal, maxVal

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

(* Phase 1a: a proposer sends a prepare message for ballot b. *)
Prepare(b) ==
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

(* Phase 2a: a proposer that received promises from a quorum asks the      *)
(* acceptors to accept a value that is safe at ballot b.                    *)
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

(* Decide: once a quorum accepted (b, v), v is chosen and announced. *)
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

---------------------------------------------------------------------------
(* Safety properties *)

(* Non-triviality: only proposed values can be learned. *)
NonTriviality ==
    /\ decision # None =>
         \E m \in msgs : m.type = "accept" /\ m.val = decision
    /\ \A d \in msgs :
         d.type = "decide" =>
            \E m \in msgs : m.type = "accept" /\ m.val = d.val

(* Consistency: once a decision is made it never changes. *)
Consistency ==
    [][decision # None => decision' = decision]_decision

(* Liveness: Paxos does not guarantee termination.  By the FLP impossibility *)
(* result, no deterministic protocol can guarantee consensus termination in *)
(* an asynchronous system in which even one process may crash; competing    *)
(* proposers may preempt each other's ballots forever.  Hence liveness is   *)
(* explicitly set to FALSE and no fairness conditions are assumed.          *)
Liveness == FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []NonTriviality
THEOREM Spec => Consistency
=============================================================================
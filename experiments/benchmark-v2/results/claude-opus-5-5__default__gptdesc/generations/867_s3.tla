------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* The Paxos consensus protocol, without explicit leaders or learners.     *)
(* Proposers and acceptors communicate by exchanging prepare, promise,     *)
(* accept, accepted and decide messages.                                   *)
(*                                                                         *)
(* The state records the set of all messages ever sent. Messages are       *)
(* never removed, which models loss, duplication and reordering. It also   *)
(* records a single representative decision value, plus three values for  *)
(* each acceptor:                                                          *)
(*   - maxBal  : the highest ballot the acceptor has seen,                 *)
(*   - maxVBal : the highest ballot in which it accepted a value,          *)
(*   - maxVal  : the value it accepted in ballot maxVBal.                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Value,     \* The set of values that can be proposed
          Acceptor,  \* The set of acceptors
          Ballot     \* The set of ballot numbers

ASSUME BallotAssump == Ballot \subseteq Nat

ASSUME AcceptorAssump == Acceptor # {} /\ IsFiniteSet(Acceptor)

None == CHOOSE v : v \notin Value

(***************************************************************************)
(* Quorums are strict majorities of acceptors. Any two of them intersect.  *)
(***************************************************************************)
Quorum == {Q \in SUBSET Acceptor : 2 * Cardinality(Q) > Cardinality(Acceptor)}

THEOREM QuorumAssump == /\ \A Q \in Quorum : Q \subseteq Acceptor
                        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Message ==
       [type : {"prepare"}, bal : Ballot]
  \cup [type : {"promise"}, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"accept"}, bal : Ballot, val : Value]
  \cup [type : {"accepted"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"decide"}, bal : Ballot, val : Value]

VARIABLES msgs,      \* The set of all messages that have been sent
          decision,  \* A representative decided value (None if undecided)
          maxBal,    \* maxBal[a]  : highest ballot seen by acceptor a
          maxVBal,   \* maxVBal[a] : highest ballot in which a accepted a value
          maxVal     \* maxVal[a]  : value accepted by a in ballot maxVBal[a]

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

(***************************************************************************)
(* Phase 1a: a proposer starts ballot b by sending a prepare message.      *)
(***************************************************************************)
Prepare(b) ==
  /\ Send([type |-> "prepare", bal |-> b])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: an acceptor promises not to take part in any lower ballot,    *)
(* and reports the last value it accepted.                                 *)
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
(* Phase 2a: after receiving promises from a quorum, a proposer asks the   *)
(* acceptors to accept value v in ballot b. If any acceptor in the quorum  *)
(* reported an accepted value, v must be the one from the highest such     *)
(* ballot. Otherwise v may be any value.                                   *)
(***************************************************************************)
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

(***************************************************************************)
(* Phase 2b: an acceptor accepts a proposal unless it has already          *)
(* promised a higher ballot.                                               *)
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
(* Decide: once a quorum of acceptors has accepted v in ballot b, v is     *)
(* chosen. A decide message is broadcast and the representative decision   *)
(* is recorded.                                                            *)
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
  \/ \E a \in Acceptor : Promise(a) \/ Accepted(a)
  \/ \E b \in Ballot, v \in Value : Accept(b, v) \/ Decide(b, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)

(* Non-triviality: only a value that has been proposed can be learned.     *)
NonTriviality ==
  decision # None =>
     \E m \in msgs : m.type = "accept" /\ m.val = decision

(* Consistency: once a value is decided, the decision never changes.       *)
Consistency ==
  [][decision # None => decision' = decision]_decision

(* All decide messages carry the same value.                               *)
Agreement ==
  \A m1, m2 \in msgs :
     (m1.type = "decide" /\ m2.type = "decide") => m1.val = m2.val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness.                                                               *)
(*                                                                         *)
(* Paxos does not guarantee termination. In an asynchronous system where   *)
(* even one process may fail by crashing, no deterministic consensus       *)
(* protocol can guarantee that a decision is eventually reached. This is   *)
(* the FLP impossibility result. For example, competing proposers can keep *)
(* preempting one another with ever higher ballots, so no value is ever    *)
(* chosen. No fairness conditions are assumed here, and the liveness       *)
(* property is set to FALSE.                                               *)
(***************************************************************************)
Liveness == FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []NonTriviality
THEOREM Spec => Consistency
=============================================================================
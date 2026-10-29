---------------------------- MODULE Paxos ----------------------------
(***************************************************************************)
(* Paxos consensus without explicit leaders or learners.                    *)
(*                                                                          *)
(* Any proposer may start a ballot by sending a "prepare" message.          *)
(* Acceptors answer with "promise" messages, a ballot's value is chosen     *)
(* and sent in an "accept" message, acceptors vote with "accepted"          *)
(* messages, and once a quorum has voted a "decide" message is sent.        *)
(*                                                                          *)
(* The variable `decision' holds a representative decided value.            *)
(*                                                                          *)
(* Liveness: Paxos does NOT guarantee termination.  By FLP-style            *)
(* reasoning, no deterministic consensus protocol can guarantee progress    *)
(* in an asynchronous system that is subject to even a single crash fault.  *)
(* Competing proposers can preempt each other forever.  For this reason     *)
(* the liveness property is explicitly FALSE.                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS any, none,
          r1, r2, r3, r4, Replicas,
          v1, v2, v3, Values,
          Ballots,
          Quorums

ASSUME /\ none \notin Values
       /\ Ballots \subseteq Nat
       /\ \A Q \in Quorums : Q \subseteq Replicas
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
       /\ \A Q \in Quorums : 2 * Cardinality(Q) > Cardinality(Replicas)

VARIABLES msgs,      \* the set of all messages ever sent
          decision,  \* a representative decided value (or none)
          maxBal,    \* maxBal[a]  : highest ballot seen by acceptor a
          maxVBal,   \* maxVBal[a] : highest ballot in which a accepted
          maxVal     \* maxVal[a]  : value accepted in ballot maxVBal[a]

vars == <<msgs, decision, maxBal, maxVBal, maxVal>>

NoBallot == -1

Messages ==
       [type : {"propose"}, val : Values]
  \cup [type : {"prepare"}, bal : Ballots]
  \cup [type : {"promise"}, acc : Replicas, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {none}]
  \cup [type : {"accept"}, bal : Ballots, val : Values]
  \cup [type : {"accepted"}, acc : Replicas, bal : Ballots, val : Values]
  \cup [type : {"decide"}, bal : Ballots, val : Values]

Send(m) == msgs' = msgs \cup {m}

ProposedValues == {m.val : m \in {mm \in msgs : mm.type = "propose"}}

-----------------------------------------------------------------------------

PaxosInit ==
  /\ msgs = {}
  /\ decision = none
  /\ maxBal  = [a \in Replicas |-> NoBallot]
  /\ maxVBal = [a \in Replicas |-> NoBallot]
  /\ maxVal  = [a \in Replicas |-> none]

(* A client proposes a value. *)
Propose(v) ==
  /\ Send([type |-> "propose", val |-> v])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(* Phase 1a: some proposer starts ballot b. *)
Prepare(b) ==
  /\ Send([type |-> "prepare", bal |-> b])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(* Phase 1b: acceptor a promises not to take part in lower ballots. *)
Promise(a) ==
  \E m \in msgs :
    /\ m.type = "prepare"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "promise", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<decision, maxVBal, maxVal>>

(* Phase 2a: a proposer picks a safe value for ballot b. *)
Accept(b, v) ==
  /\ ~ \E m \in msgs : m.type = "accept" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "promise" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ /\ Q1bv = {}
                 /\ v \in ProposedValues
              \/ \E m \in Q1bv :
                   /\ m.mval = v
                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "accept", bal |-> b, val |-> v])
  /\ UNCHANGED <<decision, maxBal, maxVBal, maxVal>>

(* Phase 2b: acceptor a votes for the value of an accept message. *)
Accepted(a) ==
  \E m \in msgs :
    /\ m.type = "accept"
    /\ m.bal >= maxBal[a]
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
    /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED decision

(* A quorum has voted for v in ballot b: v is decided. *)
Decide(b, v) ==
  /\ \E Q \in Quorums :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "accepted"
          /\ m.acc = a
          /\ m.bal = b
          /\ m.val = v
  /\ Send([type |-> "decide", bal |-> b, val |-> v])
  /\ decision' = v
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

PaxosNext ==
  \/ \E v \in Values : Propose(v)
  \/ \E b \in Ballots : Prepare(b)
  \/ \E a \in Replicas : Promise(a) \/ Accepted(a)
  \/ \E b \in Ballots, v \in Values : Accept(b, v) \/ Decide(b, v)

(* Paxos does not guarantee termination (FLP), so liveness is FALSE. *)
PaxosLiveness == FALSE

PaxosSpec == PaxosInit /\ [][PaxosNext]_vars

-----------------------------------------------------------------------------

PaxosTypeOK ==
  /\ msgs \subseteq Messages
  /\ decision \in Values \cup {none}
  /\ maxBal  \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxVBal \in [Replicas -> Ballots \cup {NoBallot}]
  /\ maxVal  \in [Replicas -> Values \cup {none}]

(* Only proposed values can be learned. *)
PaxosNontriviality ==
  /\ decision \in ProposedValues \cup {none}
  /\ \A m \in msgs : m.type = "decide" => m.val \in ProposedValues

(* Once a value is decided, the decision never changes. *)
PaxosConsistency ==
  [][decision # none => decision' = decision]_decision

PaxosSymmetry == Permutations(Replicas) \cup Permutations(Values)

=============================================================================
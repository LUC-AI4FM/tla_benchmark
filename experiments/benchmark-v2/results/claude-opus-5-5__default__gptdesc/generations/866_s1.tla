------------------------------ MODULE FastPaxos ------------------------------
(***************************************************************************)
(* A simplified specification of Lamport's Fast Paxos.                     *)
(*                                                                         *)
(*  - There is a single, unique coordinator. Its actions are Phase1a and   *)
(*    Phase2a, parameterized by ballot.                                    *)
(*  - Failures are not modeled explicitly. Agents are assumed to restore   *)
(*    their state from stable storage, and lost messages are equivalent    *)
(*    to messages that are never received.                                 *)
(*  - All agents communicate directly through the set msgs.                *)
(*  - Ballots are either fast or classic. In a fast ballot that is free    *)
(*    of constraints, the coordinator sends an "any" message. Acceptors    *)
(*    then accept proposals directly from proposers.                       *)
(*  - A collision in a fast ballot is recovered by starting a new ballot.  *)
(*    In that ballot the coordinator picks a value using the fast-quorum   *)
(*    intersection rule (O4).                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Replicas,        \* the set of acceptors
          Values,          \* the set of values that may be proposed
          Ballots,         \* the set of ballot numbers (positive naturals)
          FastBallots,     \* the subset of Ballots that are fast ballots
          ClassicQuorums,  \* the quorums used in classic ballots
          FastQuorums      \* the quorums used in fast ballots

ClassicBallots == Ballots \ FastBallots

ASSUME BallotAssumption ==
    /\ Ballots \subseteq (Nat \ {0})
    /\ FastBallots \subseteq Ballots

ASSUME QuorumAssumption ==
    /\ \A Q \in ClassicQuorums : Q \subseteq Replicas
    /\ \A Q \in FastQuorums : Q \subseteq Replicas
    /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}
    /\ \A Q \in ClassicQuorums : \A R1, R2 \in FastQuorums :
          Q \cap R1 \cap R2 # {}
    /\ \A R1, R2, R3 \in FastQuorums : R1 \cap R2 \cap R3 # {}

any  == CHOOSE v : v \notin Values
none == CHOOSE v : v \notin (Values \cup {any})

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Message ==
         [type : {"proposal"}, val : Values]
    \cup [type : {"1a"}, bal : Ballots]
    \cup [type : {"1b"}, bal : Ballots, from : Replicas,
          vbal : Ballots \cup {0}, vval : Values \cup {none}]
    \cup [type : {"2a"}, bal : Ballots, val : Values \cup {any}]
    \cup [type : {"2b"}, bal : Ballots, from : Replicas, val : Values]

VARIABLES msgs,         \* the set of all messages sent
          maxBallot,    \* maxBallot[r]: highest ballot in which r participated
          maxVBallot,   \* maxVBallot[r]: highest ballot in which r voted
          maxValue,     \* maxValue[r]: value r voted for in maxVBallot[r]
          decision      \* the set of values that have been learned/chosen

vars == <<msgs, maxBallot, maxVBallot, maxValue, decision>>

ProposedValues == {m.val : m \in {mm \in msgs : mm.type = "proposal"}}

TypeOK ==
    /\ msgs \subseteq Message
    /\ maxBallot \in [Replicas -> Ballots \cup {0}]
    /\ maxVBallot \in [Replicas -> Ballots \cup {0}]
    /\ maxValue \in [Replicas -> Values \cup {none}]
    /\ decision \subseteq Values

Init ==
    /\ msgs = {}
    /\ maxBallot = [r \in Replicas |-> 0]
    /\ maxVBallot = [r \in Replicas |-> 0]
    /\ maxValue = [r \in Replicas |-> none]
    /\ decision = {}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* A proposer proposes value v.                                            *)
(***************************************************************************)
Propose(v) ==
    /\ Send([type |-> "proposal", val |-> v])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

(***************************************************************************)
(* Phase 1a: the coordinator starts ballot b.                              *)
(***************************************************************************)
Phase1a(b) ==
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

(***************************************************************************)
(* Phase 1b: acceptor r promises to participate in ballot b.               *)
(***************************************************************************)
Phase1b(r, b) ==
    /\ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ b > maxBallot[r]
    /\ maxBallot' = [maxBallot EXCEPT ![r] = b]
    /\ Send([type |-> "1b", bal |-> b, from |-> r,
             vbal |-> maxVBallot[r], vval |-> maxValue[r]])
    /\ UNCHANGED <<maxVBallot, maxValue, decision>>

(***************************************************************************)
(* Phase 2a: the coordinator picks the value v for ballot b, or "any" in a *)
(* fast ballot. It uses the 1b messages from some classic quorum Q.        *)
(*  - If no one in Q has voted, v may be any proposed value. In a fast     *)
(*    ballot v may also be "any".                                          *)
(*  - Otherwise, let k be the highest ballot voted in, and V the values    *)
(*    voted for in k.                                                      *)
(*      * If V is a singleton, v must be its element.                      *)
(*      * If k is fast and V has several values (a collision), then:       *)
(*          - if some w satisfies O4(w), v must satisfy O4;                *)
(*          - otherwise v may be any proposed value.                       *)
(***************************************************************************)
Phase2a(b, v) ==
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
    /\ \E Q \in ClassicQuorums :
         LET M == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
             k == Max({m.vbal : m \in M})
             V == {m.vval : m \in {mm \in M : mm.vbal = k}}
             O4(w) == \E R \in FastQuorums :
                        \A a \in Q \cap R :
                          \E m \in M : /\ m.from = a
                                       /\ m.vbal = k
                                       /\ m.vval = w
         IN  /\ \A a \in Q : \E m \in M : m.from = a
             /\ IF k = 0
                  THEN \/ v \in ProposedValues
                       \/ (b \in FastBallots /\ v = any)
                  ELSE IF Cardinality(V) = 1
                         THEN v \in V
                         ELSE IF \E w \in V : O4(w)
                                THEN v \in V /\ O4(v)
                                ELSE v \in ProposedValues
    /\ Send([type |-> "2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

(***************************************************************************)
(* Phase 2b (classic): acceptor r accepts the coordinator's value in b.    *)
(***************************************************************************)
Phase2b(r, b) ==
    /\ \E m \in msgs :
         /\ m.type = "2a"
         /\ m.bal = b
         /\ m.val \in Values
         /\ b >= maxBallot[r]
         /\ maxVBallot[r] # b
         /\ maxBallot' = [maxBallot EXCEPT ![r] = b]
         /\ maxVBallot' = [maxVBallot EXCEPT ![r] = b]
         /\ maxValue' = [maxValue EXCEPT ![r] = m.val]
         /\ Send([type |-> "2b", bal |-> b, from |-> r, val |-> m.val])
    /\ UNCHANGED decision

(***************************************************************************)
(* Fast accept: in a fast ballot where the coordinator has sent "any",     *)
(* acceptor r accepts a proposed value v directly.                         *)
(***************************************************************************)
FastAccept(r, b, v) ==
    /\ b \in FastBallots
    /\ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.val = any
    /\ \E m \in msgs : m.type = "proposal" /\ m.val = v
    /\ b >= maxBallot[r]
    /\ maxVBallot[r] # b
    /\ maxBallot' = [maxBallot EXCEPT ![r] = b]
    /\ maxVBallot' = [maxVBallot EXCEPT ![r] = b]
    /\ maxValue' = [maxValue EXCEPT ![r] = v]
    /\ Send([type |-> "2b", bal |-> b, from |-> r, val |-> v])
    /\ UNCHANGED decision

(***************************************************************************)
(* Learning: value v is chosen in ballot b if a quorum of the appropriate  *)
(* kind voted for v in b.                                                  *)
(***************************************************************************)
Decide(b, v) ==
    /\ LET Qs == IF b \in FastBallots THEN FastQuorums ELSE ClassicQuorums
       IN  \E Q \in Qs :
             \A a \in Q :
               \E m \in msgs : /\ m.type = "2b"
                               /\ m.bal = b
                               /\ m.from = a
                               /\ m.val = v
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<msgs, maxBallot, maxVBallot, maxValue>>

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E b \in Ballots : Phase1a(b)
    \/ \E r \in Replicas, b \in Ballots : Phase1b(r, b)
    \/ \E b \in Ballots, v \in Values \cup {any} : Phase2a(b, v)
    \/ \E r \in Replicas, b \in Ballots : Phase2b(r, b)
    \/ \E r \in Replicas, b \in FastBallots, v \in Values : FastAccept(r, b, v)
    \/ \E b \in Ballots, v \in Values : Decide(b, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

\* Non-triviality: only proposed values can be decided.
Nontriviality == decision \subseteq ProposedValues

\* Consistency: at most one value is decided.
Consistency == Cardinality(decision) <= 1

\* Every 2b vote is for a proposed value.
VotesProposed ==
    \A m \in msgs : m.type = "2b" => m.val \in ProposedValues

Safety == TypeOK /\ Nontriviality /\ Consistency

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
=============================================================================
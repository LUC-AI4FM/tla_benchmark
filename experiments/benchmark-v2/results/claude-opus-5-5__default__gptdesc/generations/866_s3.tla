---------------------------- MODULE FastPaxos ----------------------------
(***************************************************************************)
(* A simplified specification of Lamport's Fast Paxos consensus protocol.  *)
(*                                                                         *)
(*  - There is a unique coordinator, which is not modeled as a variable.   *)
(*  - Failures are not modeled explicitly: agents keep their state in      *)
(*    stable storage. Message loss is modeled by messages never being      *)
(*    received.                                                            *)
(*  - All agents communicate directly through the set msgs.                *)
(*  - Rounds are either fast rounds (FastNum) or classic rounds            *)
(*    (ClassicNum). In a fast round the coordinator may send an "Any"      *)
(*    message, which lets acceptors vote directly for proposed values.     *)
(*    Collisions are resolved by the coordinator's value-selection rule    *)
(*    in later rounds.                                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptors,      \* set of acceptors
          Values,         \* set of values that may be proposed
          Quorums,        \* classic quorums
          FastQuorums,    \* fast quorums
          FastNum,        \* round numbers of fast rounds
          ClassicNum      \* round numbers of classic rounds

RoundNum == FastNum \cup ClassicNum

ASSUME /\ FastNum \subseteq Nat \ {0}
       /\ ClassicNum \subseteq Nat \ {0}
       /\ FastNum \cap ClassicNum = {}
       /\ IsFiniteSet(RoundNum)

ASSUME /\ Quorums \subseteq SUBSET Acceptors
       /\ FastQuorums \subseteq SUBSET Acceptors
       /\ \A Q \in Quorums : Q # {}
       /\ \A Q \in FastQuorums : Q # {}

(***************************************************************************)
(* Quorum requirements of Fast Paxos:                                      *)
(*  - any two classic quorums intersect;                                   *)
(*  - any classic quorum and any two fast quorums have a common acceptor.  *)
(***************************************************************************)
ASSUME QuorumAssumption ==
         /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
         /\ \A Q \in Quorums : \A R1, R2 \in FastQuorums :
                Q \cap R1 \cap R2 # {}

Any  == CHOOSE v : v \notin Values
None == CHOOSE v : v \notin Values \cup {Any}

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Message ==
       [type : {"propose"}, val : Values]
  \cup [type : {"1a"}, rnd : RoundNum]
  \cup [type : {"1b"}, acc : Acceptors, rnd : RoundNum,
        vrnd : RoundNum \cup {0}, vval : Values \cup {None}]
  \cup [type : {"2a"}, rnd : RoundNum, val : Values \cup {Any}]
  \cup [type : {"2b"}, acc : Acceptors, rnd : RoundNum, val : Values]

VARIABLES msgs,      \* set of all messages sent
          rnd,       \* rnd[a]  : highest round acceptor a has joined
          vrnd,      \* vrnd[a] : highest round in which a has voted
          vval,      \* vval[a] : value a voted for in round vrnd[a]
          decision   \* set of values learned as chosen

vars == <<msgs, rnd, vrnd, vval, decision>>

TypeOK ==
  /\ msgs \subseteq Message
  /\ rnd  \in [Acceptors -> RoundNum \cup {0}]
  /\ vrnd \in [Acceptors -> RoundNum \cup {0}]
  /\ vval \in [Acceptors -> Values \cup {None}]
  /\ decision \subseteq Values

Init ==
  /\ msgs = {}
  /\ rnd  = [a \in Acceptors |-> 0]
  /\ vrnd = [a \in Acceptors |-> 0]
  /\ vval = [a \in Acceptors |-> None]
  /\ decision = {}

Send(m) == msgs' = msgs \cup {m}

ProposedValues == {m.val : m \in {mm \in msgs : mm.type = "propose"}}

(***************************************************************************)
(* A proposer proposes value v.                                            *)
(***************************************************************************)
Propose(v) ==
  /\ Send([type |-> "propose", val |-> v])
  /\ UNCHANGED <<rnd, vrnd, vval, decision>>

(***************************************************************************)
(* The coordinator starts round i.                                         *)
(***************************************************************************)
Phase1a(i) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.rnd = i
  /\ Send([type |-> "1a", rnd |-> i])
  /\ UNCHANGED <<rnd, vrnd, vval, decision>>

(***************************************************************************)
(* Acceptor a joins a higher round and reports its last vote.              *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.rnd > rnd[a]
     /\ rnd' = [rnd EXCEPT ![a] = m.rnd]
     /\ Send([type |-> "1b", acc |-> a, rnd |-> m.rnd,
              vrnd |-> vrnd[a], vval |-> vval[a]])
     /\ UNCHANGED <<vrnd, vval, decision>>

(***************************************************************************)
(* The coordinator, having received 1b messages for round i from a         *)
(* classic quorum Q, picks a value according to the Fast Paxos rule:       *)
(*  - if no acceptor in Q has voted, any proposed value may be picked; in  *)
(*    a fast round the coordinator sends "Any" instead;                    *)
(*  - otherwise let k be the highest vrnd reported and V the set of values *)
(*    voted in round k. If V is a singleton, pick its element.             *)
(*  - otherwise (collision in fast round k): if some w in V could have     *)
(*    been chosen in round k, i.e. for some fast quorum R all acceptors in *)
(*    Q \cap R voted w in round k, pick w; else pick any value in V.       *)
(***************************************************************************)
Phase2a(i) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.rnd = i
  /\ \E Q \in Quorums :
       LET S == {m \in msgs : m.type = "1b" /\ m.rnd = i /\ m.acc \in Q}
       IN
       /\ \A a \in Q : \E m \in S : m.acc = a
       /\ LET k == Max({m.vrnd : m \in S})
              V == {m.vval : m \in {mm \in S : mm.vrnd = k}}
              O4(w) == \E R \in FastQuorums :
                         \A a \in Q \cap R :
                           \E m \in S : /\ m.acc = a
                                        /\ m.vrnd = k
                                        /\ m.vval = w
          IN
          IF k = 0
            THEN IF i \in FastNum
                   THEN Send([type |-> "2a", rnd |-> i, val |-> Any])
                   ELSE \E v \in ProposedValues :
                          Send([type |-> "2a", rnd |-> i, val |-> v])
            ELSE IF Cardinality(V) = 1
                   THEN \E v \in V :
                          Send([type |-> "2a", rnd |-> i, val |-> v])
                   ELSE IF \E w \in V : O4(w)
                          THEN \E w \in V :
                                 /\ O4(w)
                                 /\ Send([type |-> "2a", rnd |-> i, val |-> w])
                          ELSE \E v \in V :
                                 Send([type |-> "2a", rnd |-> i, val |-> v])
  /\ UNCHANGED <<rnd, vrnd, vval, decision>>

(***************************************************************************)
(* Acceptor a votes for the value sent by the coordinator (classic vote).  *)
(***************************************************************************)
Phase2bClassic(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.val \in Values
     /\ m.rnd >= rnd[a]
     /\ vrnd[a] < m.rnd
     /\ rnd'  = [rnd  EXCEPT ![a] = m.rnd]
     /\ vrnd' = [vrnd EXCEPT ![a] = m.rnd]
     /\ vval' = [vval EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, rnd |-> m.rnd, val |-> m.val])
     /\ UNCHANGED decision

(***************************************************************************)
(* Acceptor a, having received an "Any" message for fast round i, votes    *)
(* directly for some proposed value.                                       *)
(***************************************************************************)
Phase2bFast(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.val = Any
     /\ m.rnd \in FastNum
     /\ m.rnd >= rnd[a]
     /\ vrnd[a] < m.rnd
     /\ \E v \in ProposedValues :
          /\ rnd'  = [rnd  EXCEPT ![a] = m.rnd]
          /\ vrnd' = [vrnd EXCEPT ![a] = m.rnd]
          /\ vval' = [vval EXCEPT ![a] = v]
          /\ Send([type |-> "2b", acc |-> a, rnd |-> m.rnd, val |-> v])
     /\ UNCHANGED decision

(***************************************************************************)
(* A learner learns that v is chosen once a quorum (fast quorum in a fast  *)
(* round, classic quorum in a classic round) voted for v in round i.       *)
(***************************************************************************)
Learn ==
  \E i \in RoundNum, v \in Values :
     /\ \E Q \in (IF i \in FastNum THEN FastQuorums ELSE Quorums) :
          \A a \in Q : \E m \in msgs : /\ m.type = "2b"
                                       /\ m.acc = a
                                       /\ m.rnd = i
                                       /\ m.val = v
     /\ decision' = decision \cup {v}
     /\ UNCHANGED <<msgs, rnd, vrnd, vval>>

Next ==
  \/ \E v \in Values : Propose(v)
  \/ \E i \in RoundNum : Phase1a(i) \/ Phase2a(i)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2bClassic(a) \/ Phase2bFast(a)
  \/ Learn

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
\* Non-triviality: only proposed values can be learned.
Nontriviality ==
  \A v \in decision : \E m \in msgs : m.type = "propose" /\ m.val = v

\* Consistency: at most one value is learned.
Consistency == Cardinality(decision) <= 1

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
=============================================================================
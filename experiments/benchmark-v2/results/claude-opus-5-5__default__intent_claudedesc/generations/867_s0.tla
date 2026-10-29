------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Replicas,   \* replicas acting as both proposers and acceptors
          Values,     \* set of values that may be proposed
          Ballots,    \* set of ballot numbers; 0 is the sentinel ballot
          Quorums     \* set of quorums (strict-majority subsets of Replicas)

ASSUME /\ Ballots \subseteq Nat
       /\ 0 \in Ballots
       /\ Quorums \subseteq SUBSET Replicas
       /\ \A Q \in Quorums : 2 * Cardinality(Q) > Cardinality(Replicas)
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

Message ==
       [type : {"prepare"}, bal : Ballots]
  \cup [type : {"promise"}, acc : Replicas, bal : Ballots,
        mbal : Ballots, mval : Values \cup {None}]
  \cup [type : {"accept"}, bal : Ballots, val : Values]
  \cup [type : {"accepted"}, acc : Replicas, bal : Ballots, val : Values]

VARIABLES msgs,      \* set of all messages sent so far
          maxBal,    \* maxBal[a]: highest ballot acceptor a has promised/seen
          maxVBal,   \* maxVBal[a]: highest ballot in which a accepted a value
          maxVal,    \* maxVal[a]: value accepted by a in ballot maxVBal[a]
          decision   \* decided value, or None

vars == <<msgs, maxBal, maxVBal, maxVal, decision>>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
  /\ msgs \subseteq Message
  /\ maxBal \in [Replicas -> Ballots]
  /\ maxVBal \in [Replicas -> Ballots]
  /\ maxVal \in [Replicas -> Values \cup {None}]
  /\ decision \in Values \cup {None}

Init ==
  /\ msgs = {}
  /\ maxBal = [a \in Replicas |-> 0]
  /\ maxVBal = [a \in Replicas |-> 0]
  /\ maxVal = [a \in Replicas |-> None]
  /\ decision = None

-----------------------------------------------------------------------------
(* Phase 1a: a proposer broadcasts a Prepare for ballot b.                  *)
Prepare(b) ==
  /\ b # 0
  /\ Send([type |-> "prepare", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision>>

(* Phase 1b: acceptor a promises ballot b if it has seen no higher ballot.  *)
Promise(a) ==
  \E m \in msgs :
    /\ m.type = "prepare"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "promise", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal, decision>>

(* Phase 2a: with promises from a full quorum, propose a safe value.        *)
ProposeAccept(b, v) ==
  /\ b # 0
  /\ ~ \E m \in msgs : m.type = "accept" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET P == {m \in msgs : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
       IN  /\ \A a \in Q : \E m \in P : m.acc = a
           /\ \/ \A m \in P : m.mbal = 0
              \/ \E m \in P :
                    /\ m.mbal # 0
                    /\ m.mval = v
                    /\ \A mm \in P : mm.mbal <= m.mbal
  /\ Send([type |-> "accept", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision>>

(* Phase 2b: acceptor a accepts if it has not promised a higher ballot.     *)
Accept(a) ==
  \E m \in msgs :
    /\ m.type = "accept"
    /\ m.bal >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
    /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED decision

(* Decision: a quorum has sent Accepted for the same ballot and value.      *)
Decide ==
  /\ decision = None
  /\ \E b \in Ballots, v \in Values, Q \in Quorums :
       /\ \A a \in Q :
            [type |-> "accepted", acc |-> a, bal |-> b, val |-> v] \in msgs
       /\ decision' = v
  /\ UNCHANGED <<msgs, maxBal, maxVBal, maxVal>>

Next ==
  \/ \E b \in Ballots : Prepare(b)
  \/ \E a \in Replicas : Promise(a)
  \/ \E b \in Ballots, v \in Values : ProposeAccept(b, v)
  \/ \E a \in Replicas : Accept(a)
  \/ Decide

Spec == Init /\ [][Next]_vars /\ SF_vars(Decide)

-----------------------------------------------------------------------------
(* Safety properties                                                        *)

ProposedValues == {m.val : m \in {mm \in msgs : mm.type = "accept"}}

\* Non-triviality: only proposed values can be decided.
NonTriviality == decision = None \/ decision \in ProposedValues

\* Consistency: once a value is decided, it never changes.
Consistency == [][decision # None => decision' = decision]_vars

THEOREM Spec => [](TypeOK /\ NonTriviality)
THEOREM Spec => Consistency
=============================================================================
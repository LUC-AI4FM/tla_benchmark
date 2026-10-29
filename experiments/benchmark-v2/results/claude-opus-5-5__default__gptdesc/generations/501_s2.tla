---------------------------- MODULE MCMultiPaxos ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a MultiPaxos specification.                  *)
(*                                                                         *)
(* The file is self-contained so that SANY can parse it on its own:        *)
(*   Part 1 is the underlying MultiPaxos specification.                    *)
(*   Part 2 is the abstract ConsensusMulti specification, instantiated     *)
(*          over the values learned by MultiPaxos.                         *)
(*   Part 3 holds the checking operators and the properties to verify.     *)
(*                                                                         *)
(* Checking Spec => CSpec (refinement) causes state-space blowup, so it    *)
(* should only be run on very small constant instances, for example:       *)
(* 2 acceptors, 2 ballots, 1 or 2 slots, and 2 values. The invariants      *)
(* TypeOK, Nontriviality and Consistency are cheaper and can be checked on *)
(* larger instances.                                                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors,   \* set of acceptors
          Values,      \* set of proposable values
          Quorums,     \* set of quorums (subsets of Acceptors)
          Ballots,     \* finite set of ballot numbers (naturals)
          Slots        \* finite set of log slots (instances)

ASSUME QuorumAssumption ==
         /\ Quorums \subseteq SUBSET Acceptors
         /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

VARIABLES msgs,     \* set of all messages sent so far
          maxBal,   \* maxBal[a] : highest ballot that acceptor a has joined
          votes,    \* votes[a]  : set of votes cast by acceptor a
          learned   \* learned[s]: set of values learned for slot s

vars == <<msgs, maxBal, votes, learned>>

(***************************************************************************)
(* Part 1: the MultiPaxos specification                                    *)
(***************************************************************************)
VoteRec == [bal : Ballots, slot : Slots, val : Values]

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots, voted : SUBSET VoteRec]
  \cup [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ msgs = {}
  /\ maxBal = [a \in Acceptors |-> -1]
  /\ votes = [a \in Acceptors |-> {}]
  /\ learned = [s \in Slots |-> {}]

\* A leader starts ballot b.
Phase1a(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, votes, learned>>

\* Acceptor a joins a higher ballot and reports its votes for all slots.
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, voted |-> votes[a]])
    /\ UNCHANGED <<votes, learned>>

\* The leader of ballot b proposes value v for slot s.
Phase2a(b, s, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       LET M1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
           V   == UNION { {r \in m.voted : r.slot = s} : m \in M1b }
       IN  /\ \A a \in Q : \E m \in M1b : m.acc = a
           /\ \/ V = {}
              \/ \E r \in V : /\ r.val = v
                              /\ \A r2 \in V : r2.bal <= r.bal
  /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
  /\ UNCHANGED <<maxBal, votes, learned>>

\* Acceptor a votes for a proposal.
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ votes' = [votes EXCEPT ![a] =
                   @ \cup {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]}]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal,
             slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED learned

ChosenIn(s, v) ==
  \E b \in Ballots, Q \in Quorums :
    \A a \in Q : \E m \in msgs :
      /\ m.type = "2b" /\ m.acc = a /\ m.bal = b
      /\ m.slot = s /\ m.val = v

\* A learner learns a value that a quorum voted for in the same ballot.
Learn(s, v) ==
  /\ v \notin learned[s]
  /\ ChosenIn(s, v)
  /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
  /\ UNCHANGED <<msgs, maxBal, votes>>

Next ==
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
  \/ \E b \in Ballots, s \in Slots, v \in Values : Phase2a(b, s, v)
  \/ \E s \in Slots, v \in Values : Learn(s, v)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Part 2: the ConsensusMulti specification, instantiated with            *)
(* chosen <- learned. For each slot, at most one value is chosen, and once *)
(* chosen it never changes.                                                *)
(***************************************************************************)
CInit == learned = [s \in Slots |-> {}]

CNext ==
  \E s \in Slots, v \in Values :
    /\ learned[s] = {}
    /\ learned' = [learned EXCEPT ![s] = {v}]

CSpec == CInit /\ [][CNext]_learned

(***************************************************************************)
(* Part 3: checking operators                                              *)
(***************************************************************************)
TypeOK ==
  /\ msgs \subseteq Message
  /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
  /\ votes \in [Acceptors -> SUBSET VoteRec]
  /\ learned \in [Slots -> SUBSET Values]

\* Only proposable values can be learned.
Nontriviality ==
  \A s \in Slots : learned[s] \subseteq Values

\* At most one value is learned per slot.
Consistency ==
  \A s \in Slots : Cardinality(learned[s]) <= 1

THEOREM Spec => []TypeOK
THEOREM Spec => CSpec            \* small instances only (state-space blowup)
THEOREM Spec => []Nontriviality
THEOREM Spec => []Consistency
=============================================================================
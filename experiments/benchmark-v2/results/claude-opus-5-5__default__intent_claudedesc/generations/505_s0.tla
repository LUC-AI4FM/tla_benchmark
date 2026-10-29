------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Single-decree Paxos consensus with a fixed proposer (no leader          *)
(* election). Messages are kept in a set and are never removed, so they    *)
(* may be delayed, delivered in any order, or delivered more than once.    *)
(* Message loss and corruption are not modeled.                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Values,      \* the set of values that can be proposed
          Acceptors,   \* the set of acceptor processes
          Quorums,     \* the set of quorums (subsets of Acceptors)
          Ballots      \* the set of ballot numbers (natural numbers)

ASSUME /\ IsFiniteSet(Acceptors)
       /\ Cardinality(Acceptors) >= 3
       /\ Cardinality(Values) >= 2
       /\ Ballots \subseteq Nat
       /\ Quorums \subseteq SUBSET Acceptors
       /\ Quorums # {}
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal,   \* maxBal[a]: highest ballot acceptor a has promised/participated in
          maxVBal,  \* maxVBal[a]: highest ballot in which a accepted a value
          maxVal,   \* maxVal[a]: the value a accepted in ballot maxVBal[a]
          msgs      \* the set of all messages sent

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
  /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal  \in [Acceptors -> Values \cup {None}]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal  = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal  = [a \in Acceptors |-> None]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Phase 1a: the (fixed) proposer starts ballot b by broadcasting a        *)
(* prepare request.                                                        *)
(***************************************************************************)
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: acceptor a promises not to take part in ballots lower than    *)
(* m.bal and reports the last value it accepted (if any).                  *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2a: having received 1b messages from a quorum for ballot b, the   *)
(* proposer sends an accept request. If some acceptor in the quorum has    *)
(* accepted a value, the value of the highest such ballot must be used.    *)
(***************************************************************************)
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b: acceptor a accepts the proposal unless it has promised a      *)
(* higher ballot.                                                          *)
(***************************************************************************)
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
  \/ \E b \in Ballots : Phase1a(b) \/ \E v \in Values : Phase2a(b, v)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Acceptor a has accepted value v in ballot b.
VotedFor(a, b, v) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.acc = a
                  /\ m.bal = b
                  /\ m.val = v

\* Value v is chosen at ballot b: a quorum accepted v in ballot b.
ChosenAt(b, v) ==
  \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

\* Value v is chosen if a quorum accepted it in some ballot.
Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

chosen == {v \in Values : Chosen(v)}

\* Consensus Safety: values accepted by quorums (at any ballot numbers)
\* are always identical; different values are never both chosen.
ConsensusSafety ==
  \A v1, v2 \in Values :
    (Chosen(v1) /\ Chosen(v2)) => (v1 = v2)

\* Single Value Agreement: at most one value is ever chosen.
SingleValueAgreement == Cardinality(chosen) <= 1

\* An acceptor never accepts two different values in the same ballot.
OneValuePerBallot ==
  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
    VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

\* Once a value is chosen it stays chosen (stability of the decision).
ChosenStable ==
  \A v \in Values : [](Chosen(v) => [](Chosen(v)))

THEOREM Spec => [](TypeOK /\ ConsensusSafety /\ SingleValueAgreement
                   /\ OneValuePerBallot)
=============================================================================
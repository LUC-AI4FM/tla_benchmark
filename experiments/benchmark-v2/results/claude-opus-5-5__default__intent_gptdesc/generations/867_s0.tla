------------------------------ MODULE SingleDecreePaxos ------------------------------
(***************************************************************************)
(* Single-decree Paxos at the message-passing level.                       *)
(*                                                                         *)
(* Message passing: messages go into the set msgs and are never removed.   *)
(* Any action may read any message at any time, and may read it more than  *)
(* once. This models delay, duplication and reordering. Leader election,   *)
(* timers and delivery order are not modelled.                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors,   \* finite set of acceptors
          Proposers,   \* finite set of proposers
          Values,      \* set of values that may be proposed
          Ballots,     \* finite set of ballot numbers (natural numbers)
          Owner        \* Owner[b] is the unique proposer that owns ballot b

ASSUME /\ IsFiniteSet(Acceptors)
       /\ Acceptors # {}
       /\ Proposers # {}
       /\ Values # {}
       /\ Ballots \subseteq Nat
       /\ Owner \in [Ballots -> Proposers]   \* each ballot has exactly one owner

None == CHOOSE v : v \notin Values

NoBallot == -1

(***************************************************************************)
(* Quorums are majorities, so any two quorums overlap.                     *)
(***************************************************************************)
Quorums == {Q \in SUBSET Acceptors : 2 * Cardinality(Q) > Cardinality(Acceptors)}

QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME QuorumIntersection

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]
  \cup [type : {"decide"}, bal : Ballots, val : Values]

VARIABLES maxBal,    \* maxBal[a]: highest ballot acceptor a has promised
          maxVBal,   \* maxVBal[a]: highest ballot in which a has accepted a value
          maxVal,    \* maxVal[a]: the value a accepted in ballot maxVBal[a]
          msgs,      \* set of all messages sent so far
          proposed,  \* set of values proposed by some proposer
          decided    \* set of values that have been decided

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, decided>>

TypeOK ==
  /\ maxBal   \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxVBal  \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxVal   \in [Acceptors -> Values \cup {None}]
  /\ msgs     \subseteq Message
  /\ proposed \subseteq Values
  /\ decided  \subseteq Values

Init ==
  /\ maxBal   = [a \in Acceptors |-> NoBallot]
  /\ maxVBal  = [a \in Acceptors |-> NoBallot]
  /\ maxVal   = [a \in Acceptors |-> None]
  /\ msgs     = {}
  /\ proposed = {}
  /\ decided  = {}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* A proposer proposes a value. This value becomes a candidate value.      *)
(***************************************************************************)
Propose(p, v) ==
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, decided>>

(***************************************************************************)
(* Phase 1a: the owner of ballot b starts round b by sending Prepare.      *)
(***************************************************************************)
Phase1a(p, b) ==
  /\ Owner[b] = p
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

(***************************************************************************)
(* Phase 1b: an acceptor promises a ballot higher than any it has          *)
(* promised. It reports the last value it accepted.                        *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal, proposed, decided>>

(***************************************************************************)
(* Phase 2a: the owner of ballot b has promises from a quorum Q.           *)
(*  - If no member of Q reported an accepted value, it may send any        *)
(*    proposed value.                                                      *)
(*  - Otherwise it must send the value reported with the highest ballot.   *)
(* At most one Accept request is sent per ballot.                          *)
(***************************************************************************)
Phase2a(p, b, v) ==
  /\ Owner[b] = p
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ /\ \A m \in Q1b : m.mbal = NoBallot
                 /\ v \in proposed
              \/ \E m \in Q1b :
                   /\ m.mbal # NoBallot
                   /\ m.mval = v
                   /\ \A mm \in Q1b : mm.mbal <= m.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts an Accept request only if doing so does   *)
(* not break a promise it made earlier.                                    *)
(***************************************************************************)
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED <<proposed, decided>>

(***************************************************************************)
(* Decision: a value is decided once a quorum of acceptors have sent       *)
(* matching Accepted messages for the same ballot and value.               *)
(***************************************************************************)
Decide(b, v) ==
  /\ \E Q \in Quorums :
       \A a \in Q : [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs
  /\ decided' = decided \cup {v}
  /\ Send([type |-> "decide", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed>>

Next ==
  \/ \E p \in Proposers, v \in Values : Propose(p, v)
  \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
  \/ \E a \in Acceptors : Phase1b(a)
  \/ \E p \in Proposers, b \in Ballots, v \in Values : Phase2a(p, b, v)
  \/ \E a \in Acceptors : Phase2b(a)
  \/ \E b \in Ballots, v \in Values : Decide(b, v)

\* Safety only. No fairness conditions; termination is not required.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Derived notions                                                         *)
(***************************************************************************)
VotedFor(a, b, v) == [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen == {v \in Values : \E b \in Ballots : ChosenAt(b, v)}

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedFor(a, b, v)
                    /\ maxBal[a] > b

SafeAt(v, b) ==
  \A c \in Ballots :
    c < b => \E Q \in Quorums :
               \A a \in Q : VotedFor(a, c, v) \/ WontVoteIn(a, c)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Consistency: at most one value is ever chosen or decided.
Consistency ==
  /\ \A v1, v2 \in decided : v1 = v2
  /\ \A v1, v2 \in Chosen  : v1 = v2

\* Validity: every decided or chosen value was proposed by some proposer.
Validity == /\ decided \subseteq proposed
            /\ Chosen  \subseteq proposed

\* A value is decided only when it was in fact chosen by a quorum.
DecidedImpliesChosen == decided \subseteq Chosen

\* Acceptor state is well formed.
AcceptorInv ==
  \A a \in Acceptors :
    /\ maxVBal[a] <= maxBal[a]
    /\ (maxVBal[a] = NoBallot) <=> (maxVal[a] = None)
    /\ maxVBal[a] # NoBallot =>
         [type |-> "2a", bal |-> maxVBal[a], val |-> maxVal[a]] \in msgs

\* Message invariants. These are the inductive core of Paxos safety.
MsgInv ==
  \A m \in msgs :
    /\ (m.type = "1b") =>
         /\ m.bal <= maxBal[m.acc]
         /\ m.mbal < m.bal
         /\ (m.mbal = NoBallot) <=> (m.mval = None)
         /\ m.mbal # NoBallot =>
              [type |-> "2a", bal |-> m.mbal, val |-> m.mval] \in msgs
    /\ (m.type = "2a") =>
         /\ SafeAt(m.val, m.bal)
         /\ m.val \in proposed
         /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal) => mm = m
    /\ (m.type = "2b") =>
         /\ [type |-> "2a", bal |-> m.bal, val |-> m.val] \in msgs
         /\ m.bal <= maxVBal[m.acc]
    /\ (m.type = "decide") =>
         /\ ChosenAt(m.bal, m.val)
         /\ m.val \in decided

\* Combined state invariant.
Inv ==
  /\ TypeOK
  /\ QuorumIntersection
  /\ AcceptorInv
  /\ MsgInv
  /\ Consistency
  /\ Validity
  /\ DecidedImpliesChosen

(***************************************************************************)
(* Monotonicity of acceptor state, stated as an action property.          *)
(* - The promised ballot never decreases.                                  *)
(* - The accepted ballot never decreases.                                  *)
(* - The accepted value changes only when the accepted ballot increases.   *)
(* - Messages, proposals and decisions are never removed.                  *)
(***************************************************************************)
MonotonicStep ==
  /\ \A a \in Acceptors :
       /\ maxBal'[a]  >= maxBal[a]
       /\ maxVBal'[a] >= maxVBal[a]
       /\ (maxVBal'[a] = maxVBal[a]) => (maxVal'[a] = maxVal[a])
  /\ msgs \subseteq msgs'
  /\ proposed \subseteq proposed'
  /\ decided \subseteq decided'

Monotonicity == [][MonotonicStep]_vars

\* Once a value is decided, it stays decided.
DecisionStable == \A v \in Values : [](v \in decided => [](v \in decided))

THEOREM Spec => []Inv
THEOREM Spec => Monotonicity
=============================================================================
------------------------------ MODULE MCPaxosConsensus ------------------------------
(***************************************************************************)
(* Model-checking wrapper for Paxos consensus.                             *)
(*                                                                         *)
(* The Paxos specification is included directly in this module, and so    *)
(* is the single-value consensus abstraction, so that the module is        *)
(* self-contained and parses with SANY. The module:                        *)
(*  - defines helper operators over votes and chosen values;               *)
(*  - states invariants on message validity, acceptor validity and         *)
(*    consistency;                                                         *)
(*  - connects Paxos to the Consensus abstraction by mapping the           *)
(*    abstract "chosen" set to the set of values chosen by Paxos.          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Value, Acceptor, Quorum, MaxBallot

ASSUME QuorumAssumption ==
          /\ \A Q \in Quorum : Q \subseteq Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

ASSUME MaxBallotAssumption == MaxBallot \in Nat

\* Finite set of ballots, so that the model can be checked.
Ballot == 0..MaxBallot

None == CHOOSE v : v \notin Value

Message ==
       [type : {"1a"}, bal : Ballot]
  \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"2a"}, bal : Ballot, val : Value]
  \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

VARIABLES maxBal,   \* maxBal[a]: highest ballot acceptor a has participated in
          maxVBal,  \* maxVBal[a]: highest ballot in which a has voted
          maxVal,   \* maxVal[a]: value a voted for in ballot maxVBal[a]
          msgs      \* set of all messages that have been sent

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
  /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVal  \in [Acceptor -> Value \cup {None}]
  /\ msgs \subseteq Message

-----------------------------------------------------------------------------
(* Paxos actions                                                           *)

Init ==
  /\ maxBal  = [a \in Acceptor |-> -1]
  /\ maxVBal = [a \in Acceptor |-> -1]
  /\ maxVal  = [a \in Acceptor |-> None]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
  /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum :
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

Phase2b(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[a]
     /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
  \/ \E b \in Ballot : \/ Phase1a(b)
                       \/ \E v \in Value : Phase2a(b, v)
  \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper definitions about votes and chosen values                        *)

votes ==
  [a \in Acceptor |->
     {<<m.bal, m.val>> : m \in {mm \in msgs : /\ mm.type = "2b"
                                              /\ mm.acc = a}}]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

WontVoteIn(a, b) == /\ DidNotVoteIn(a, b)
                    /\ maxBal[a] > b

SafeAt(b, v) ==
  \A c \in 0..(b-1) :
     \E Q \in Quorum :
        \A a \in Q : VotedFor(a, c, v) \/ WontVoteIn(a, c)

-----------------------------------------------------------------------------
(* Invariants                                                              *)

VotesSafe ==
  \A a \in Acceptor, b \in Ballot, v \in Value :
     VotedFor(a, b, v) => SafeAt(b, v)

OneValuePerBallot ==
  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
     VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

MsgInv ==
  \A m \in msgs :
    /\ (m.type = "1b") =>
          /\ m.bal =< maxBal[m.acc]
          /\ \/ /\ m.mval \in Value
                /\ m.mbal \in Ballot
                /\ VotedFor(m.acc, m.mbal, m.mval)
             \/ /\ m.mval = None
                /\ m.mbal = -1
          /\ \A c \in (m.mbal + 1)..(m.bal - 1) : DidNotVoteIn(m.acc, c)
    /\ (m.type = "2a") =>
          /\ SafeAt(m.bal, m.val)
          /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
    /\ (m.type = "2b") =>
          /\ \E ma \in msgs : /\ ma.type = "2a"
                              /\ ma.bal  = m.bal
                              /\ ma.val  = m.val
          /\ m.bal =< maxBal[m.acc]

AccInv ==
  \A a \in Acceptor :
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]
    /\ (maxVBal[a] >= 0) => VotedFor(a, maxVBal[a], maxVal[a])
    /\ \A c \in Ballot : c > maxVBal[a] => DidNotVoteIn(a, c)

Consistency == \A v, w \in chosen : v = w

ChosenAtMostOne == Cardinality(chosen) =< 1

Inv == TypeOK /\ MsgInv /\ AccInv

-----------------------------------------------------------------------------
(* Single-value consensus abstraction, with its "chosen" set mapped to the *)
(* values chosen by Paxos (inlined form of                                 *)
(*   C == INSTANCE Consensus WITH chosen <- chosen).                       *)

CInit == chosen = {}

CNext == /\ chosen = {}
         /\ \E v \in Value : chosen' = {v}

CTypeOK == /\ chosen \subseteq Value
           /\ IsFiniteSet(chosen)

CInv == /\ CTypeOK
        /\ Cardinality(chosen) =< 1

CSpec == CInit /\ [][CNext]_chosen

\* Paxos implements consensus: Spec => CSpec
THEOREM Refinement == Spec => CSpec

THEOREM Invariance == Spec => [](Inv /\ VotesSafe /\ OneValuePerBallot /\ Consistency)
=============================================================================
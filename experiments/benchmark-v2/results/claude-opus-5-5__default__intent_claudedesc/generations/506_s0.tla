---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Value, Acceptor, Quorum, MaxBallot

ASSUME QuorumAssumption ==
          /\ \A Q \in Quorum : Q \subseteq Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

ASSUME MaxBallotAssumption == MaxBallot \in Nat

Ballot == 0..MaxBallot

None == CHOOSE v : v \notin Value

Message ==
       [type : {"1a"}, bal : Ballot]
  \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"2a"}, bal : Ballot, val : Value]
  \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

VARIABLES maxBal,   \* highest ballot each acceptor has promised (prepared)
          maxVBal,  \* highest ballot in which each acceptor has voted
          maxVal,   \* value voted for in ballot maxVBal
          msgs      \* set of all messages ever sent

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
  /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVal  \in [Acceptor -> Value \cup {None}]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal  = [a \in Acceptor |-> -1]
  /\ maxVBal = [a \in Acceptor |-> -1]
  /\ maxVal  = [a \in Acceptor |-> None]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* Phase 1a: a proposer requests promises for ballot b *)
Phase1a(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(* Phase 1b: an acceptor promises ballot m.bal and reports its last vote *)
Phase1b(a) ==
  /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal>>

(* Phase 2a: proposer proposes value v in ballot b, given a quorum of 1b's *)
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

(* Phase 2b: acceptor accepts a proposal *)
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
(* Voting abstractions *)

VotedFor(a, b, v) == [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

WontVoteIn(a, b) == /\ \A v \in Value : ~ VotedFor(a, b, v)
                    /\ maxBal[a] > b

SafeAt(b, v) ==
  \A c \in 0..(b-1) :
    \E Q \in Quorum :
      \A a \in Q : VotedFor(a, c, v) \/ WontVoteIn(a, c)

-----------------------------------------------------------------------------
(* Safety properties *)

Consistency == \A v1, v2 \in chosen : v1 = v2

MsgInv ==
  \A m \in msgs :
    /\ (m.type = "1b") =>
          /\ m.bal =< maxBal[m.acc]
          /\ (m.mbal >= 0) => VotedFor(m.acc, m.mbal, m.mval)
          /\ (m.mbal = -1) <=> (m.mval = None)
          /\ \A c \in (m.mbal + 1)..(m.bal - 1) :
                \A v \in Value : ~ VotedFor(m.acc, c, v)
    /\ (m.type = "2a") =>
          /\ SafeAt(m.bal, m.val)
          /\ \A ma \in msgs : (ma.type = "2a" /\ ma.bal = m.bal)
                                 => ma.val = m.val
    /\ (m.type = "2b") =>
          /\ \E ma \in msgs : /\ ma.type = "2a"
                              /\ ma.bal = m.bal
                              /\ ma.val = m.val
          /\ m.bal =< maxVBal[m.acc]

AccInv ==
  \A a \in Acceptor :
    /\ maxBal[a] >= maxVBal[a]
    /\ (maxVBal[a] = -1) <=> (maxVal[a] = None)
    /\ (maxVBal[a] >= 0) => VotedFor(a, maxVBal[a], maxVal[a])
    /\ \A c \in Ballot : c > maxVBal[a] => \A v \in Value : ~ VotedFor(a, c, v)

Inv == TypeOK /\ AccInv /\ MsgInv /\ Consistency

-----------------------------------------------------------------------------
(* Refinement of an abstract consensus specification *)

chosenBar == chosen

ConsInit == chosenBar = {}

ConsNext == /\ chosenBar = {}
            /\ \E v \in Value : chosenBar' = {v}

ConsSpec == ConsInit /\ [][ConsNext]_chosenBar

ConsTypeOK == chosenBar \subseteq Value /\ Cardinality(chosenBar) =< 1

(* Action property: once a value is chosen, the chosen set never changes *)
ChosenStable == [][chosenBar # {} => chosenBar' = chosenBar]_vars

THEOREM Spec => []Inv
THEOREM Spec => ConsSpec

-----------------------------------------------------------------------------
(* Symmetry for model checking *)
Symmetry == Permutations(Acceptor) \cup Permutations(Value)

=============================================================================
------------------------------ MODULE Paxos ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Ballots, Quorums, Values

ASSUME BallotsAssump == Ballots \subseteq Nat
ASSUME QuorumAssump ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal,   \* highest ballot promised by each acceptor
          maxVBal,  \* highest ballot in which each acceptor accepted
          maxVal,   \* value accepted in maxVBal
          msgs      \* set of all messages sent (async, may be delayed/reordered)

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

(* The stable leader starts ballot b by sending a prepare request. *)
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(* Acceptor a promises ballot b, reporting its last accepted proposal. *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal>>

(* The leader, having promises from a quorum, proposes a safe value. *)
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                   /\ m.mval = v
                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(* Acceptor a accepts unless it has promised a higher ballot. *)
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
(* Safety *)

VotedFor(a, b, v) == \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

Proposed(v) == \E m \in msgs : m.type = "2a" /\ m.val = v

Agreement == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

Integrity == \A v \in Values \cup {None} : Chosen(v) => (v \in Values /\ Proposed(v))

NonContradiction ==
  \A a \in Acceptors, b \in Ballots, v1, v2 \in Values :
     VotedFor(a, b, v1) /\ VotedFor(a, b, v2) => v1 = v2

OneValuePerBallot ==
  \A m1, m2 \in msgs :
     m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal => m1.val = m2.val

Inv == TypeOK /\ Agreement /\ Integrity /\ NonContradiction /\ OneValuePerBallot

-----------------------------------------------------------------------------
(* Optional liveness assumptions, kept separate from safety *)

LiveSpec ==
  /\ Spec
  /\ \A a \in Acceptors : WF_vars(Phase1b(a)) /\ WF_vars(Phase2b(a))

=============================================================================
------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* Single-decree Paxos consensus with leader election omitted.            *)
(* Ballot numbers are natural numbers. Communication is asynchronous       *)
(* message passing: messages are never removed from the set msgs, so they  *)
(* may be received in any order and any number of times, but are never    *)
(* lost or corrupted.                                                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Value,      \* the set of values that may be proposed
          Acceptor,   \* the set of acceptor processes
          Quorum      \* the set of quorums (sets of acceptors)

ASSUME QuorumAssumption ==
          /\ Cardinality(Acceptor) >= 3
          /\ \A Q \in Quorum : Q \subseteq Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {}

Ballot == Nat

None == CHOOSE v : v \notin Value
  \* The special "no value" marker, distinct from every proposable value.

Message ==
       [type : {"1a"}, bal : Ballot]
  \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"2a"}, bal : Ballot, val : Value]
  \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

VARIABLES maxBal,   \* maxBal[a]: highest ballot acceptor a has promised/seen
          maxVBal,  \* maxVBal[a]: highest ballot in which a has voted
          maxVal,   \* maxVal[a]: the value a voted for in ballot maxVBal[a]
          msgs      \* the set of all messages ever sent

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

(***************************************************************************)
(* Phase 1a: the leader initiates ballot b (at most once per ballot).      *)
(***************************************************************************)
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: an acceptor receiving a 1a message with a ballot higher than  *)
(* any it has seen promises not to accept lower ballots and reports its   *)
(* last vote.                                                              *)
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
(* Phase 2a: having received 1b messages for ballot b from a quorum, the   *)
(* leader proposes a value: the value of the highest-numbered reported     *)
(* vote, or any value if none was reported. At most one 2a per ballot.     *)
(***************************************************************************)
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

(***************************************************************************)
(* Phase 2b: an acceptor votes for a proposal unless it has promised a     *)
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
  \/ \E b \in Ballot : \/ Phase1a(b)
                       \/ \E v \in Value : Phase2a(b, v)
  \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Voting and choosing                                                     *)
(***************************************************************************)
VotedForIn(a, v, b) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.acc = a
                  /\ m.bal = b
                  /\ m.val = v

ChosenIn(v, b) == \E Q \in Quorum : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballot : ChosenIn(v, b)

ChosenSet == {v \in Value : Chosen(v)}

Proposed(v) == \E m \in msgs : m.type = "2a" /\ m.val = v

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Agreement: at most one value is ever chosen.
Agreement == \A v1, v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

\* Once a value is chosen, no other value can ever be chosen.
StableAgreement ==
  \A v \in Value : [](Chosen(v) => [](\A w \in Value : Chosen(w) => w = v))

\* Validity: any chosen value was proposed.
Validity == \A v \in Value : Chosen(v) => Proposed(v)

\* At most one proposal per ballot.
OneProposalPerBallot ==
  \A m1, m2 \in msgs :
    (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1 = m2

\* Votes in the same ballot are for the same value.
VotesSafeInBallot ==
  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
    VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => v1 = v2

Inv == TypeOK /\ Agreement /\ Validity /\ OneProposalPerBallot
                /\ VotesSafeInBallot

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness under assumptions                                              *)
(* The system "stabilizes" with a single leader using ballot b, which is   *)
(* the highest ballot ever started, and a quorum Q of acceptors that keep  *)
(* taking steps (weak fairness). Under these assumptions some value is     *)
(* eventually chosen.                                                      *)
(***************************************************************************)
LiveAssumption(b, Q) ==
  /\ [][\A c \in Ballot : c > b => ~Phase1a(c)]_vars
  /\ WF_vars(Phase1a(b))
  /\ WF_vars(\E v \in Value : Phase2a(b, v))
  /\ \A a \in Q : WF_vars(Phase1b(a)) /\ WF_vars(Phase2b(a))

LiveSpec == Spec /\ \E b \in Ballot, Q \in Quorum : LiveAssumption(b, Q)

Liveness == <>(\E v \in Value : Chosen(v))

THEOREM Spec => []Inv
THEOREM Spec => StableAgreement
THEOREM LiveSpec => Liveness
=============================================================================
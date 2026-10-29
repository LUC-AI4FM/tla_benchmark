---- MODULE PaxosProposals ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS minValue, Tuples

ConstMinValue == 0
ConstTuples == {<<1>>, <<2>>}

Acceptors == {"a1", "a2", "a3"}
Ballots   == minValue .. (minValue + 2)
NoBallot  == minValue - 1
None      == <<>>
Quorums   == {Q \in SUBSET Acceptors : 2 * Cardinality(Q) > Cardinality(Acceptors)}

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Tuples \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Tuples]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Tuples]

VARIABLES maxBal,    \* acceptor persistent: highest promised ballot
          maxVBal,   \* acceptor persistent: ballot of last accepted proposal
          maxVal,    \* acceptor persistent: value of last accepted proposal
          votes,     \* history: all <<bal, val>> pairs accepted by each acceptor
          msgs,      \* network (messages may be lost)
          proposals, \* proposer state: proposals issued (one per ballot)
          decided    \* set of decided <<bal, val>> pairs

vars == <<maxBal, maxVBal, maxVal, votes, msgs, proposals, decided>>

TypeOK ==
  /\ maxBal    \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxVBal   \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxVal    \in [Acceptors -> Tuples \cup {None}]
  /\ votes     \in [Acceptors -> SUBSET (Ballots \X Tuples)]
  /\ msgs      \subseteq Messages
  /\ proposals \subseteq [bal : Ballots, val : Tuples]
  /\ decided   \subseteq (Ballots \X Tuples)

Init ==
  /\ maxBal    = [a \in Acceptors |-> NoBallot]
  /\ maxVBal   = [a \in Acceptors |-> NoBallot]
  /\ maxVal    = [a \in Acceptors |-> None]
  /\ votes     = [a \in Acceptors |-> {}]
  /\ msgs      = {}
  /\ proposals = {}
  /\ decided   = {}

Send(m) == msgs' = msgs \cup {m}

\* Proposer starts a ballot: send prepare request
Phase1a(b) ==
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, proposals, decided>>

\* Acceptor promises, reporting its last accepted proposal
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal, votes, proposals, decided>>

\* Proposer collects promises from a majority and picks a consistent value
Phase2a(b, v) ==
  /\ ~ \E p \in proposals : p.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal # NoBallot}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                   /\ m.mval = v
                   /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ proposals' = proposals \cup {[bal |-> b, val |-> v]}
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, decided>>

\* Acceptor accepts unless it has promised a higher ballot
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
    /\ votes'   = [votes   EXCEPT ![a] = @ \cup {<<m.bal, m.val>>}]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED <<proposals, decided>>

\* A value is decided once accepted by a majority at a ballot
Decide(b, v) ==
  /\ <<b, v>> \notin decided
  /\ \E Q \in Quorums : \A a \in Q :
       \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v
  /\ decided' = decided \cup {<<b, v>>}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, msgs, proposals>>

\* Message loss
LoseMsg ==
  \E m \in msgs :
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, proposals, decided>>

Next ==
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
  \/ \E b \in Ballots, v \in Tuples : Phase2a(b, v) \/ Decide(b, v)
  \/ LoseMsg

Spec == Init /\ [][Next]_vars

\* Liveness variant: a single proposer (highest ballot) proceeds alone with
\* reliable delivery (no loss steps required for progress).
MaxB == minValue + 2
LiveNext ==
  \/ Phase1a(MaxB)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
  \/ \E v \in Tuples : Phase2a(MaxB, v) \/ Decide(MaxB, v)
LiveSpec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Phase1a(MaxB))
  /\ \A a \in Acceptors : WF_vars(Phase1b(a)) /\ WF_vars(Phase2b(a))
  /\ WF_vars(\E v \in Tuples : Phase2a(MaxB, v))
  /\ WF_vars(\E v \in Tuples : Decide(MaxB, v))
EventuallyDecided == <>(decided # {})

----------------------------------------------------------------------------
\* Safety invariants

Agreement ==
  \A d1, d2 \in decided : d1[2] = d2[2]

SlotAgreement ==
  \A d1, d2 \in decided : d1[1] = d2[1] => d1[2] = d2[2]

PromiseRespected ==
  \A a \in Acceptors :
    /\ maxVBal[a] <= maxBal[a]
    /\ \A vt \in votes[a] : vt[1] <= maxBal[a]

AcceptedWasProposed ==
  \A a \in Acceptors : \A vt \in votes[a] :
    [bal |-> vt[1], val |-> vt[2]] \in proposals

UniqueProposalPerBallot ==
  \A p1, p2 \in proposals : p1.bal = p2.bal => p1.val = p2.val

ProposalsCarryForward ==
  \A p \in proposals : \A d \in decided :
    d[1] <= p.bal => p.val = d[2]

DecidedByMajority ==
  \A d \in decided : \E Q \in Quorums : \A a \in Q : d \in votes[a]

Inv ==
  /\ TypeOK
  /\ Agreement
  /\ SlotAgreement
  /\ PromiseRespected
  /\ AcceptedWasProposed
  /\ UniqueProposalPerBallot
  /\ ProposalsCarryForward
  /\ DecidedByMajority

DecidedImmutable == [][\A d \in decided : d \in decided']_vars

THEOREM SafetyTheorem == Spec => []Inv
THEOREM ImmutabilityTheorem == Spec => DecidedImmutable
THEOREM LivenessTheorem == LiveSpec => EventuallyDecided
====
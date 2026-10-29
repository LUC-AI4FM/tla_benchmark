------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Proposers,      \* set of proposers
    Acceptors,      \* set of acceptors
    Learners,       \* set of learners
    Values,         \* set of proposable values
    Slots,          \* set of independent consensus instances (slots)
    MaxBallot,      \* highest ballot number (ballots are 0..MaxBallot)
    Quorums,        \* set of quorums of acceptors
    None,           \* a non-value
    Leader,         \* distinguished proposer used only for the liveness assumption
    GoodQ           \* distinguished quorum of non-faulty acceptors (liveness only)

Ballots == 0..MaxBallot

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q \in Quorums : Q # {}
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME ConstantsAssumption ==
    /\ None \notin Values
    /\ MaxBallot \in Nat
    /\ Leader \in Proposers
    /\ GoodQ \in Quorums

VARIABLES
    msgs,       \* set of all messages ever sent (messages in transit / delivered)
    pBallot,    \* pBallot[p]: current ballot of proposer p (-1 = none)
    maxBal,     \* maxBal[a]: highest ballot promised by acceptor a
    maxVBal,    \* maxVBal[a][s]: highest ballot in which a voted in slot s
    maxVal,     \* maxVal[a][s]: value voted by a in ballot maxVBal[a][s]
    votes,      \* votes[a]: set of all votes [slot, bal, val] cast by a
    proposed,   \* proposed[s]: set of values proposed for slot s
    learned     \* learned[l][s]: set of values learned by l for slot s

vars == <<msgs, pBallot, maxBal, maxVBal, maxVal, votes, proposed, learned>>

-----------------------------------------------------------------------------
Messages ==
       [type : {"1a"}, from : Proposers, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mvbal : [Slots -> Ballots \cup {-1}],
        mval  : [Slots -> Values \cup {None}]]
  \cup [type : {"2a"}, from : Proposers, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

Vote == [slot : Slots, bal : Ballots, val : Values]

TypeOK ==
    /\ msgs \subseteq Messages
    /\ pBallot \in [Proposers -> Ballots \cup {-1}]
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> [Slots -> Ballots \cup {-1}]]
    /\ maxVal \in [Acceptors -> [Slots -> Values \cup {None}]]
    /\ votes \in [Acceptors -> SUBSET Vote]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Learners -> [Slots -> SUBSET Values]]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ pBallot = [p \in Proposers |-> -1]
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> [s \in Slots |-> -1]]
    /\ maxVal = [a \in Acceptors |-> [s \in Slots |-> None]]
    /\ votes = [a \in Acceptors |-> {}]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [l \in Learners |-> [s \in Slots |-> {}]]

\* A proposer (client request) introduces a value for a slot.
Propose(p, s, v) ==
    /\ v \notin proposed[s]
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, pBallot, maxBal, maxVBal, maxVal, votes, learned>>

\* Phase 1a: proposer p starts a new, higher ballot b (covers all slots).
Phase1a(p, b) ==
    /\ b > pBallot[p]
    /\ pBallot' = [pBallot EXCEPT ![p] = b]
    /\ Send([type |-> "1a", from |-> p, bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, proposed, learned>>

\* Phase 1b: acceptor a promises ballot m.bal and reports its votes per slot.
Phase1b(a, m) ==
    /\ m \in msgs
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mvbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<pBallot, maxVBal, maxVal, votes, proposed, learned>>

\* Value v is safe to propose in slot s at ballot b given 1b messages from quorum Q.
SafeAt(s, b, v, Q) ==
    LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
    IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
        /\ \/ \A m \in Q1b : m.mvbal[s] = -1
           \/ \E m \in Q1b :
                 /\ m.mvbal[s] # -1
                 /\ m.mval[s] = v
                 /\ \A m2 \in Q1b : m2.mvbal[s] =< m.mvbal[s]

\* Phase 2a: proposer p proposes v for slot s in its current ballot.
\* At most one 2a message per (ballot, slot) (abstracts unique ballot ownership).
Phase2a(p, s, v) ==
    LET b == pBallot[p] IN
    /\ b \in Ballots
    /\ v \in proposed[s]
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums : SafeAt(s, b, v, Q)
    /\ Send([type |-> "2a", from |-> p, bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<pBallot, maxBal, maxVBal, maxVal, votes, proposed, learned>>

\* Phase 2b: acceptor a votes for the proposal in m.
Phase2b(a, m) ==
    /\ m \in msgs
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ [slot |-> m.slot, bal |-> m.bal, val |-> m.val] \notin votes[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a][m.slot] = m.val]
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[slot |-> m.slot, bal |-> m.bal, val |-> m.val]}]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED <<pBallot, proposed, learned>>

\* Learner l learns v for slot s after seeing 2b messages from a quorum in one ballot.
Learn(l, s, v) ==
    /\ v \notin learned[l][s]
    /\ \E b \in Ballots, Q \in Quorums :
          \A a \in Q : \E m \in msgs :
              /\ m.type = "2b" /\ m.acc = a /\ m.bal = b
              /\ m.slot = s /\ m.val = v
    /\ learned' = [learned EXCEPT ![l][s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, pBallot, maxBal, maxVBal, maxVal, votes, proposed>>

Next ==
    \/ \E p \in Proposers, s \in Slots, v \in Values : Propose(p, s, v)
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors, m \in msgs : Phase1b(a, m)
    \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
    \/ \E a \in Acceptors, m \in msgs : Phase2b(a, m)
    \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Chosen: a quorum of acceptors voted for v in the same slot and ballot. *)
ChosenAt(s, b, v) ==
    \E Q \in Quorums : \A a \in Q : [slot |-> s, bal |-> b, val |-> v] \in votes[a]

Chosen(s, v) == \E b \in Ballots : ChosenAt(s, b, v)

(* Safety invariants *)
ChosenConsistency ==
    \A s \in Slots : \A v1, v2 \in Values :
        (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2

LearnedConsistency ==
    \A s \in Slots : \A l1, l2 \in Learners :
        \A v1 \in learned[l1][s], v2 \in learned[l2][s] : v1 = v2

LearnedIsChosen ==
    \A l \in Learners, s \in Slots : \A v \in learned[l][s] : Chosen(s, v)

Nontriviality ==
    /\ \A l \in Learners, s \in Slots : learned[l][s] \subseteq proposed[s]
    /\ \A s \in Slots, v \in Values : Chosen(s, v) => v \in proposed[s]

SafetyInv ==
    /\ TypeOK
    /\ ChosenConsistency
    /\ LearnedConsistency
    /\ LearnedIsChosen
    /\ Nontriviality

(* Stability: learned sets only grow *)
Stability ==
    [][\A l \in Learners, s \in Slots : learned[l][s] \subseteq learned'[l][s]]_learned

ChosenStable ==
    \A s \in Slots, v \in Values : [](Chosen(s, v) => [](Chosen(s, v)))

-----------------------------------------------------------------------------
(* Liveness under favorable conditions *)

\* Leader starts a new ballot only when its current ballot cannot succeed.
LeaderNeedsNewBallot ==
    \/ pBallot[Leader] = -1
    \/ \E a \in Acceptors : maxBal[a] > pBallot[Leader]
    \/ \E p \in Proposers \ {Leader} : pBallot[p] = pBallot[Leader]

LeaderPrepare ==
    /\ LeaderNeedsNewBallot
    /\ \E b \in Ballots : Phase1a(Leader, b)

Fairness ==
    /\ WF_vars(LeaderPrepare)
    /\ WF_vars(\E s \in Slots, v \in Values : Phase2a(Leader, s, v))
    /\ \A a \in GoodQ :
          /\ WF_vars(\E m \in msgs : Phase1b(a, m))
          /\ WF_vars(\E m \in msgs : Phase2b(a, m))
    /\ \A l \in Learners :
          WF_vars(\E s \in Slots, v \in Values : Learn(l, s, v))

LiveSpec == Spec /\ Fairness

\* Partial synchrony assumption: eventually only the Leader starts new ballots,
\* and the Leader eventually holds a ballot exceeding every promise.
EventuallyLeaderAlone ==
    <>[][\A p \in Proposers \ {Leader} : pBallot'[p] = pBallot[p]]_pBallot

EventuallyLeaderHighest ==
    <>(/\ pBallot[Leader] \in Ballots
       /\ \A p \in Proposers \ {Leader} : pBallot[p] < pBallot[Leader]
       /\ \A a \in Acceptors : maxBal[a] =< pBallot[Leader])

SomeProposal == \E s \in Slots : proposed[s] # {}

\* Progress: if a proposal is made and the system eventually stabilizes
\* with a unique leader and a live quorum, some value is eventually chosen
\* and learned by every learner.
Progress ==
    (EventuallyLeaderAlone /\ EventuallyLeaderHighest /\ <>SomeProposal)
        => <>(\E s \in Slots, v \in Values :
                 Chosen(s, v) /\ \A l \in Learners : v \in learned[l][s])

\* Once chosen, a value is eventually learned by all learners.
ChosenLearned ==
    \A s \in Slots, v \in Values :
        Chosen(s, v) ~> (\A l \in Learners : v \in learned[l][s])

THEOREM Spec => []SafetyInv
THEOREM Spec => Stability
THEOREM LiveSpec => Progress
=============================================================================
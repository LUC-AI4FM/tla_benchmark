------------------------------- MODULE MultiPaxosConsensus -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Proposers, Acceptors, Quorums, Learners, Values, Slots, Ballots

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ Quorums # {}
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

ConstBallots == 0..2

SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

None == -1

VARIABLES msgs,            \* set of messages ever sent
          proposed,        \* proposed[s] : values proposed for slot s
          pBallot,         \* pBallot[p] : current ballot of proposer p
          maxBal,          \* maxBal[a] : highest ballot promised by acceptor a
          votes,           \* votes[a][s] : set of [bal, val] votes cast by a for slot s
          learned          \* learned[l][s] : values learned by learner l for slot s

vars == <<msgs, proposed, pBallot, maxBal, votes, learned>>

VoteRec == [bal : Ballots, val : Values]

Messages ==
         [type : {"1a"}, bal : Ballots]
    \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
          votes : [Slots -> SUBSET VoteRec]]
    \cup [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
    \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

TypeOK ==
    /\ msgs \subseteq Messages
    /\ proposed \in [Slots -> SUBSET Values]
    /\ pBallot \in [Proposers -> Ballots \cup {None}]
    /\ maxBal \in [Acceptors -> Ballots \cup {None}]
    /\ votes \in [Acceptors -> [Slots -> SUBSET VoteRec]]
    /\ learned \in [Learners -> [Slots -> SUBSET Values]]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ proposed = [s \in Slots |-> {}]
    /\ pBallot = [p \in Proposers |-> None]
    /\ maxBal = [a \in Acceptors |-> None]
    /\ votes = [a \in Acceptors |-> [s \in Slots |-> {}]]
    /\ learned = [l \in Learners |-> [s \in Slots |-> {}]]

\* A client/proposer proposes value v for slot s
Propose(p, s, v) ==
    /\ v \notin proposed[s]
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, pBallot, maxBal, votes, learned>>

\* Proposer p starts a new (higher) ballot b
Phase1a(p, b) ==
    /\ pBallot[p] = None \/ b > pBallot[p]
    /\ pBallot' = [pBallot EXCEPT ![p] = b]
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<proposed, maxBal, votes, learned>>

\* Acceptor a promises ballot m.bal and reports its votes for all slots
Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ maxBal[a] = None \/ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, votes |-> votes[a]])
        /\ UNCHANGED <<proposed, pBallot, votes, learned>>

\* Value v is safe to propose at ballot b for slot s given 1b messages from quorum Q
SafeAt(Q, b, s, v) ==
    LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
        reported == UNION {m.votes[s] : m \in Q1b}
    IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
        /\ \/ reported = {}
           \/ \E r \in reported :
                 /\ r.val = v
                 /\ \A r2 \in reported : r2.bal <= r.bal

Phase2a(p, s, v) ==
    LET b == pBallot[p] IN
    /\ b # None
    /\ v \in proposed[s]
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums : SafeAt(Q, b, s, v)
    /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<proposed, pBallot, maxBal, votes, learned>>

Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ maxBal[a] = None \/ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ votes' = [votes EXCEPT ![a][m.slot] = @ \cup {[bal |-> m.bal, val |-> m.val]}]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<proposed, pBallot, learned>>

Learn(l, s, v) ==
    /\ \E b \in Ballots, Q \in Quorums :
          \A a \in Q : [type |-> "2b", acc |-> a, bal |-> b, slot |-> s, val |-> v] \in msgs
    /\ learned' = [learned EXCEPT ![l][s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, proposed, pBallot, maxBal, votes>>

Next ==
    \/ \E p \in Proposers, s \in Slots, v \in Values : Propose(p, s, v)
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------------
\* Chosen: a quorum of acceptors voted for v in the same ballot for slot s
ChosenAt(b, s, v) ==
    \E Q \in Quorums : \A a \in Q : [bal |-> b, val |-> v] \in votes[a][s]

Chosen(s, v) == \E b \in Ballots : ChosenAt(b, s, v)

LearnedVals(s) == UNION {learned[l][s] : l \in Learners}

NontrivialityInv ==
    /\ \A l \in Learners, s \in Slots : learned[l][s] \subseteq proposed[s]
    /\ \A s \in Slots, v \in Values : Chosen(s, v) => v \in proposed[s]

ConsistencyInv ==
    /\ \A s \in Slots : \A v1, v2 \in LearnedVals(s) : v1 = v2
    /\ \A s \in Slots : \A v1, v2 \in Values :
          (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2

Stability ==
    [][\A l \in Learners, s \in Slots : learned[l][s] \subseteq learned'[l][s]]_vars

\* Abstract consensus specification satisfied by the protocol
ConsensusSpec ==
    /\ [](\A s \in Slots : Cardinality(LearnedVals(s)) <= 1)
    /\ [](\A s \in Slots : LearnedVals(s) \subseteq proposed[s])
    /\ Stability

-----------------------------------------------------------------------------------------
\* Liveness under favorable conditions: a single proposer that eventually runs
\* uncontested and a quorum of acceptors and learners that keep taking steps.
FairSpec ==
    /\ Spec
    /\ \A p \in Proposers, s \in Slots, v \in Values : WF_vars(Phase2a(p, s, v))
    /\ \A a \in Acceptors : WF_vars(Phase1b(a)) /\ WF_vars(Phase2b(a))
    /\ \A l \in Learners, s \in Slots, v \in Values : WF_vars(Learn(l, s, v))

Progress ==
    (\E s \in Slots : proposed[s] # {}) ~> (\E s \in Slots, v \in Values : Chosen(s, v))

=========================================================================================
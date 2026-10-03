---------------------------- MODULE FastPaxos ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* Set of acceptor agents
    Values,         \* Set of proposable values
    Quorum,         \* Set of classic quorums
    FastQuorum,     \* Set of fast quorums
    MaxRound        \* Maximum round number to bound the model

VARIABLES
    proposed,       \* Set of values that have been proposed
    round,          \* Current round number
    votes,          \* votes[a] = record of acceptor a's vote: [rnd |-> r, val |-> v]
    decision,       \* Set of decided values
    msgs            \* Set of messages in the network

vars == <<proposed, round, votes, decision, msgs>>

None == CHOOSE v : v \notin Values

Rounds == 0..MaxRound

\* Message types
Message ==
    [type : {"1a"}, rnd : Rounds] \cup
    [type : {"1b"}, rnd : Rounds, acc : Acceptors, mbal : Rounds \cup {-1}, mval : Values \cup {None}] \cup
    [type : {"2a"}, rnd : Rounds, val : Values] \cup
    [type : {"2b"}, rnd : Rounds, acc : Acceptors, val : Values] \cup
    [type : {"propose"}, val : Values]

\* Type invariant
FastTypeOK ==
    /\ proposed \subseteq Values
    /\ round \in Rounds
    /\ votes \in [Acceptors -> [rnd : Rounds \cup {-1}, val : Values \cup {None}]]
    /\ decision \subseteq Values
    /\ msgs \subseteq Message

\* Initial state
Init ==
    /\ proposed = {}
    /\ round = 0
    /\ votes = [a \in Acceptors |-> [rnd |-> -1, val |-> None]]
    /\ decision = {}
    /\ msgs = {}

\* A proposer proposes a value
Propose(v) ==
    /\ v \in Values
    /\ msgs' = msgs \cup {[type |-> "propose", val |-> v]}
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED <<round, votes, decision>>

\* Coordinator starts a new round (Phase 1a)
Phase1a(r) ==
    /\ r \in Rounds
    /\ r > round
    /\ round' = r
    /\ msgs' = msgs \cup {[type |-> "1a", rnd |-> r]}
    /\ UNCHANGED <<proposed, votes, decision>>

\* Acceptor responds to Phase 1a (Phase 1b)
Phase1b(a, r) ==
    /\ [type |-> "1a", rnd |-> r] \in msgs
    /\ votes[a].rnd < r
    /\ msgs' = msgs \cup {[type |-> "1b", rnd |-> r, acc |-> a, 
                           mbal |-> votes[a].rnd, mval |-> votes[a].val]}
    /\ UNCHANGED <<proposed, round, votes, decision>>

\* Get all 1b messages for a given round
Msgs1b(r) == {m \in msgs : m.type = "1b" /\ m.rnd = r}

\* Get the set of acceptors that sent 1b messages for round r
Acceptors1b(r) == {m.acc : m \in Msgs1b(r)}

\* Find the highest ballot voted in 1b messages
HighestBallot(S) ==
    LET ballots == {m.mbal : m \in S}
    IN IF ballots = {} \/ ballots = {-1} THEN -1
       ELSE CHOOSE b \in ballots : \A b2 \in ballots : b >= b2

\* Values voted at the highest ballot
ValuesAtHighest(S) ==
    LET hb == HighestBallot(S)
    IN IF hb = -1 THEN {}
       ELSE {m.mval : m \in {m2 \in S : m2.mbal = hb /\ m2.mval # None}}

\* Classic Phase 2a - coordinator picks a value based on 1b responses
Phase2aClassic(r, v) ==
    /\ r \in Rounds
    /\ r > 0
    /\ [type |-> "propose", val |-> v] \in msgs
    /\ \E Q \in Quorum :
        /\ Q \subseteq Acceptors1b(r)
        /\ LET S == {m \in Msgs1b(r) : m.acc \in Q}
               vals == ValuesAtHighest(S)
           IN \/ vals = {}  \* No previous votes, free to choose
              \/ v \in vals \* Must choose from highest voted values
    /\ \A m \in msgs : ~(m.type = "2a" /\ m.rnd = r)  \* No 2a sent for this round yet
    /\ msgs' = msgs \cup {[type |-> "2a", rnd |-> r, val |-> v]}
    /\ UNCHANGED <<proposed, round, votes, decision>>

\* Fast round - round 0 allows direct voting on proposed values
Phase2aFast(v) ==
    /\ round = 0
    /\ [type |-> "propose", val |-> v] \in msgs
    /\ msgs' = msgs \cup {[type |-> "2a", rnd |-> 0, val |-> v]}
    /\ UNCHANGED <<proposed, round, votes, decision>>

\* Acceptor votes in Phase 2b
Phase2b(a, r, v) ==
    /\ [type |-> "2a", rnd |-> r, val |-> v] \in msgs
    /\ votes[a].rnd < r \/ (votes[a].rnd = r /\ r = 0)  \* Can vote multiple times in fast round 0
    /\ votes' = [votes EXCEPT ![a] = [rnd |-> r, val |-> v]]
    /\ msgs' = msgs \cup {[type |-> "2b", rnd |-> r, acc |-> a, val |-> v]}
    /\ UNCHANGED <<proposed, round, decision>>

\* Get 2b messages for a round
Msgs2b(r) == {m \in msgs : m.type = "2b" /\ m.rnd = r}

\* Decide based on classic quorum
DecideClassic(r, v) ==
    /\ r > 0
    /\ \E Q \in Quorum :
        \A a \in Q : [type |-> "2b", rnd |-> r, acc |-> a, val |-> v] \in msgs
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<proposed, round, votes, msgs>>

\* Decide based on fast quorum (for round 0)
DecideFast(v) ==
    /\ \E Q \in FastQuorum :
        \A a \in Q : [type |-> "2b", rnd |-> 0, acc |-> a, val |-> v] \in msgs
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<proposed, round, votes, msgs>>

\* Recovery action for collision in fast round - coordinator picks based on fast quorum intersection
Phase2aRecovery(r, v) ==
    /\ r > 0
    /\ \E Q \in Quorum :
        /\ Q \subseteq Acceptors1b(r)
        /\ LET S == {m \in Msgs1b(r) : m.acc \in Q}
               hb == HighestBallot(S)
           IN /\ hb = 0  \* Previous round was fast round
              /\ \E FQ \in FastQuorum :
                   LET fqVotes == {m \in S : m.acc \in FQ /\ m.mbal = 0}
                       fqVals == {m.mval : m \in fqVotes}
                   IN /\ Cardinality(fqVotes) >= Cardinality(FQ)  \* All FQ members voted
                      /\ v \in fqVals
    /\ \A m \in msgs : ~(m.type = "2a" /\ m.rnd = r)
    /\ msgs' = msgs \cup {[type |-> "2a", rnd |-> r, val |-> v]}
    /\ UNCHANGED <<proposed, round, votes, decision>>

\* Next state relation
Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E r \in Rounds : Phase1a(r)
    \/ \E a \in Acceptors, r \in Rounds : Phase1b(a, r)
    \/ \E r \in Rounds, v \in Values : Phase2aClassic(r, v)
    \/ \E v \in Values : Phase2aFast(v)
    \/ \E a \in Acceptors, r \in Rounds, v \in Values : Phase2b(a, r, v)
    \/ \E r \in Rounds, v \in Values : DecideClassic(r, v)
    \/ \E v \in Values : DecideFast(v)
    \/ \E r \in Rounds, v \in Values : Phase2aRecovery(r, v)

\* Specification
FastSpec == Init /\ [][Next]_vars

\* Safety: decided values must have been proposed (non-triviality)
FastNontriviality == decision \subseteq proposed

\* Consistency: at most one value is decided (agreement)
PaxosConsistency == Cardinality(decision) <= 1

=============================================================================
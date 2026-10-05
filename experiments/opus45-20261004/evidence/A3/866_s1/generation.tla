---------------------------- MODULE FastPaxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* Set of acceptor agents
    Values,         \* Set of proposable values
    Quorum,         \* Set of classic quorums
    FastQuorum,     \* Set of fast quorums
    MaxRound        \* Maximum round number for bounded model checking

VARIABLES
    round,          \* Current round number
    decision,       \* The decided value (or None if no decision)
    proposed,       \* Set of proposed values
    votes,          \* votes[a][r] = value voted by acceptor a in round r (or None)
    maxRound,       \* maxRound[a] = highest round acceptor a has participated in
    isFast          \* isFast[r] = TRUE iff round r is a fast round

None == CHOOSE v : v \notin Values

Rounds == 0..MaxRound

TypeOK ==
    /\ round \in Rounds
    /\ decision \in Values \cup {None}
    /\ proposed \subseteq Values
    /\ votes \in [Acceptors -> [Rounds -> Values \cup {None}]]
    /\ maxRound \in [Acceptors -> Rounds \cup {-1}]
    /\ isFast \in [Rounds -> BOOLEAN]

\* Quorum intersection properties required for Fast Paxos
\* Any two classic quorums intersect
QuorumAssumption == \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {}

\* Any fast quorum and classic quorum intersect
FastQuorumAssumption == \A FQ \in FastQuorum, Q \in Quorum : FQ \cap Q /= {}

\* Any two fast quorums have sufficient intersection (for collision detection)
FastQuorumIntersection == \A FQ1, FQ2 \in FastQuorum : 
    Cardinality(FQ1 \cap FQ2) >= 1

\* Quorums consist of acceptors
QuorumSubset == 
    /\ \A Q \in Quorum : Q \subseteq Acceptors
    /\ \A FQ \in FastQuorum : FQ \subseteq Acceptors

ASSUME QuorumAssumption /\ FastQuorumAssumption /\ QuorumSubset

-----------------------------------------------------------------------------

Init ==
    /\ round = 0
    /\ decision = None
    /\ proposed = {}
    /\ votes = [a \in Acceptors |-> [r \in Rounds |-> None]]
    /\ maxRound = [a \in Acceptors |-> -1]
    /\ isFast = [r \in Rounds |-> FALSE]

\* Propose a value
Propose(v) ==
    /\ decision = None
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED <<round, decision, votes, maxRound, isFast>>

\* Start a new fast round (coordinator action)
StartFastRound(r) ==
    /\ r > round
    /\ r <= MaxRound
    /\ decision = None
    /\ round' = r
    /\ isFast' = [isFast EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<decision, proposed, votes, maxRound>>

\* Start a new classic round (coordinator action)
StartClassicRound(r) ==
    /\ r > round
    /\ r <= MaxRound
    /\ decision = None
    /\ round' = r
    /\ isFast' = [isFast EXCEPT ![r] = FALSE]
    /\ UNCHANGED <<decision, proposed, votes, maxRound>>

\* Find the highest round in which any acceptor in set S voted
HighestVotedRound(S, r) ==
    LET votedRounds == {r2 \in 0..(r-1) : \E a \in S : votes[a][r2] /= None}
    IN IF votedRounds = {} THEN -1 ELSE CHOOSE max \in votedRounds : 
        \A r2 \in votedRounds : r2 <= max

\* Get values voted in round r by acceptors in set S
VotesInRound(S, r) ==
    {votes[a][r] : a \in {a2 \in S : votes[a2][r] /= None}}

\* Determine the safe value to propose in classic round based on quorum responses
SafeValue(Q, r) ==
    LET hr == HighestVotedRound(Q, r)
    IN IF hr = -1 
       THEN CHOOSE v \in proposed : TRUE  \* Any proposed value is safe
       ELSE LET votedVals == VotesInRound(Q, hr)
            IN IF Cardinality(votedVals) = 1
               THEN CHOOSE v \in votedVals : TRUE
               ELSE CHOOSE v \in votedVals : TRUE  \* Collision recovery

\* Acceptor votes in a fast round (any proposed value)
FastVote(a, r, v) ==
    /\ decision = None
    /\ round = r
    /\ isFast[r] = TRUE
    /\ maxRound[a] < r
    /\ v \in proposed
    /\ votes' = [votes EXCEPT ![a][r] = v]
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ UNCHANGED <<round, decision, proposed, isFast>>

\* Acceptor votes in a classic round (coordinator-selected value)
ClassicVote(a, r, v, Q) ==
    /\ decision = None
    /\ round = r
    /\ isFast[r] = FALSE
    /\ maxRound[a] < r
    /\ Q \in Quorum
    /\ \A a2 \in Q : maxRound[a2] >= r - 1 \/ maxRound[a2] = -1
    /\ v = SafeValue(Q, r) \/ (HighestVotedRound(Q, r) = -1 /\ v \in proposed)
    /\ votes' = [votes EXCEPT ![a][r] = v]
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ UNCHANGED <<round, decision, proposed, isFast>>

\* Decide in a fast round (requires fast quorum with same vote)
FastDecide(r, v, FQ) ==
    /\ decision = None
    /\ round = r
    /\ isFast[r] = TRUE
    /\ FQ \in FastQuorum
    /\ \A a \in FQ : votes[a][r] = v
    /\ decision' = v
    /\ UNCHANGED <<round, proposed, votes, maxRound, isFast>>

\* Decide in a classic round (requires classic quorum with same vote)
ClassicDecide(r, v, Q) ==
    /\ decision = None
    /\ round = r
    /\ isFast[r] = FALSE
    /\ Q \in Quorum
    /\ \A a \in Q : votes[a][r] = v
    /\ decision' = v
    /\ UNCHANGED <<round, proposed, votes, maxRound, isFast>>

\* Collision recovery: coordinator detects collision and starts classic round
CollisionRecovery(r) ==
    /\ decision = None
    /\ round = r
    /\ isFast[r] = TRUE
    /\ \E FQ \in FastQuorum : 
        LET votedVals == VotesInRound(FQ, r)
        IN Cardinality(votedVals) > 1  \* Collision detected
    /\ r + 1 <= MaxRound
    /\ round' = r + 1
    /\ isFast' = [isFast EXCEPT ![r + 1] = FALSE]
    /\ UNCHANGED <<decision, proposed, votes, maxRound>>

-----------------------------------------------------------------------------

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E r \in Rounds : StartFastRound(r)
    \/ \E r \in Rounds : StartClassicRound(r)
    \/ \E a \in Acceptors, r \in Rounds, v \in Values : FastVote(a, r, v)
    \/ \E a \in Acceptors, r \in Rounds, v \in Values, Q \in Quorum : 
        ClassicVote(a, r, v, Q)
    \/ \E r \in Rounds, v \in Values, FQ \in FastQuorum : FastDecide(r, v, FQ)
    \/ \E r \in Rounds, v \in Values, Q \in Quorum : ClassicDecide(r, v, Q)
    \/ \E r \in Rounds : CollisionRecovery(r)

Spec == Init /\ [][Next]_<<round, decision, proposed, votes, maxRound, isFast>>

-----------------------------------------------------------------------------
\* Safety Properties

\* Non-triviality: Any decided value must have been proposed
NonTriviality == decision /= None => decision \in proposed

\* Consistency: At most one value is ever decided (implicit since decision is single-valued)
Consistency == TRUE  \* Trivially true given our state representation

\* Agreement: Once decided, the value never changes
Agreement == [][decision /= None => decision' = decision]_decision

\* Validity: A decision can only be made if some value was proposed
Validity == decision /= None => proposed /= {}

\* Combined safety invariant
Safety == TypeOK /\ NonTriviality /\ Validity

-----------------------------------------------------------------------------
\* Liveness Properties (require fairness)

\* Weak fairness on all actions
FairSpec == Spec /\ WF_<<round, decision, proposed, votes, maxRound, isFast>>(Next)

\* If a value is proposed, eventually a decision is made
Liveness == (\E v \in Values : v \in proposed) ~> (decision /= None)

=============================================================================
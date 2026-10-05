------------------------------- MODULE FastPaxos -------------------------------
(******************************************************************************)
(* A simplified specification of Leslie Lamport's Fast Paxos consensus        *)
(* protocol. This specification assumes a unique coordinator, omits explicit  *)
(* modeling of failures (since agents restore state from stable storage), and *)
(* allows all agents to communicate directly. The protocol models both fast   *)
(* and classic rounds, with special handling for quorum intersection and      *)
(* value selection in the presence of collisions.                             *)
(******************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* Set of acceptor agents
    Values,         \* Set of proposable values
    FastRounds,     \* Set of fast round numbers
    ClassicRounds,  \* Set of classic round numbers
    Quorums,        \* Set of classic quorums
    FastQuorums     \* Set of fast quorums

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorums : Q \subseteq Acceptors
    /\ \A Q \in FastQuorums : Q \subseteq Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
    /\ \A Q1, Q2 \in FastQuorums : Q1 \cap Q2 # {}
    /\ \A Q \in Quorums : \A FQ1, FQ2 \in FastQuorums : Q \cap FQ1 \cap FQ2 # {}

Rounds == FastRounds \cup ClassicRounds

None == CHOOSE v : v \notin Values

VARIABLES
    proposed,       \* Set of values that have been proposed
    votes,          \* votes[a][r] = vote cast by acceptor a in round r (or None)
    maxBal,         \* maxBal[a] = highest ballot acceptor a has participated in
    decision,       \* decision[r] = value decided in round r (or None)
    coordVal        \* coordVal[r] = value coordinator selected for round r (or None)

vars == <<proposed, votes, maxBal, decision, coordVal>>

(******************************************************************************)
(* Type invariant                                                             *)
(******************************************************************************)
TypeOK ==
    /\ proposed \subseteq Values
    /\ votes \in [Acceptors -> [Rounds -> Values \cup {None}]]
    /\ maxBal \in [Acceptors -> Rounds \cup {-1}]
    /\ decision \in [Rounds -> Values \cup {None}]
    /\ coordVal \in [Rounds -> Values \cup {None}]

(******************************************************************************)
(* Helper definitions                                                         *)
(******************************************************************************)

\* Votes cast in a round
VotesInRound(r) == {<<a, votes[a][r]>> : a \in {b \in Acceptors : votes[b][r] # None}}

\* Acceptors that voted in round r
VotedInRound(r) == {a \in Acceptors : votes[a][r] # None}

\* Values voted for in round r
ValuesVotedInRound(r) == {votes[a][r] : a \in VotedInRound(r)}

\* Check if a value was voted by a quorum in round r
ChosenInRound(v, r) ==
    IF r \in FastRounds
    THEN \E FQ \in FastQuorums : \A a \in FQ : votes[a][r] = v
    ELSE \E Q \in Quorums : \A a \in Q : votes[a][r] = v

\* A value is chosen if it was chosen in some round
Chosen(v) == \E r \in Rounds : ChosenInRound(v, r)

\* Find the highest round <= r in which acceptor a voted
MaxVotedRound(a, r) ==
    LET validRounds == {r2 \in Rounds : r2 < r /\ votes[a][r2] # None}
    IN IF validRounds = {} THEN -1
       ELSE CHOOSE r2 \in validRounds : \A r3 \in validRounds : r3 <= r2

\* Get votes from acceptors in quorum Q for rounds < r
QuorumVotes(Q, r) ==
    {<<a, r2, votes[a][r2]>> : a \in Q, r2 \in {r3 \in Rounds : r3 < r /\ votes[a][r3] # None}}

\* Find the maximum round with a vote in a set of votes
MaxRoundInVotes(voteSet) ==
    IF voteSet = {} THEN -1
    ELSE LET rounds == {r : <<a, r, v>> \in voteSet}
         IN CHOOSE r \in rounds : \A r2 \in rounds : r2 <= r

\* Safe value selection for coordinator in classic round
SafeValue(Q, r) ==
    LET qvotes == QuorumVotes(Q, r)
        maxR == MaxRoundInVotes(qvotes)
    IN IF maxR = -1 THEN None
       ELSE LET maxVotes == {<<a, r2, v>> \in qvotes : r2 = maxR}
                vals == {v : <<a, r2, v>> \in maxVotes}
            IN IF Cardinality(vals) = 1 
               THEN CHOOSE v \in vals : TRUE
               ELSE None

(******************************************************************************)
(* Initial state                                                              *)
(******************************************************************************)
Init ==
    /\ proposed = {}
    /\ votes = [a \in Acceptors |-> [r \in Rounds |-> None]]
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ decision = [r \in Rounds |-> None]
    /\ coordVal = [r \in Rounds |-> None]

(******************************************************************************)
(* Actions                                                                    *)
(******************************************************************************)

\* A proposer proposes a value
Propose(v) ==
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED <<votes, maxBal, decision, coordVal>>

\* Coordinator starts a classic round by selecting a value
CoordinatorSelectValue(r, v) ==
    /\ r \in ClassicRounds
    /\ coordVal[r] = None
    /\ v \in proposed
    /\ \E Q \in Quorums :
        /\ \A a \in Q : maxBal[a] < r
        /\ LET sv == SafeValue(Q, r)
           IN IF sv = None THEN TRUE ELSE v = sv
    /\ coordVal' = [coordVal EXCEPT ![r] = v]
    /\ UNCHANGED <<proposed, votes, maxBal, decision>>

\* Coordinator starts a fast round (allows any proposed value)
CoordinatorStartFastRound(r) ==
    /\ r \in FastRounds
    /\ coordVal[r] = None
    /\ \E Q \in Quorums : \A a \in Q : maxBal[a] < r
    /\ coordVal' = [coordVal EXCEPT ![r] = CHOOSE v \in Values : TRUE]  \* Marker that round is open
    /\ UNCHANGED <<proposed, votes, maxBal, decision>>

\* Acceptor votes in a classic round
AcceptorVoteClassic(a, r, v) ==
    /\ r \in ClassicRounds
    /\ coordVal[r] = v
    /\ maxBal[a] < r
    /\ votes[a][r] = None
    /\ votes' = [votes EXCEPT ![a][r] = v]
    /\ maxBal' = [maxBal EXCEPT ![a] = r]
    /\ UNCHANGED <<proposed, decision, coordVal>>

\* Acceptor votes in a fast round (can vote for any proposed value)
AcceptorVoteFast(a, r, v) ==
    /\ r \in FastRounds
    /\ v \in proposed
    /\ maxBal[a] < r
    /\ votes[a][r] = None
    /\ votes' = [votes EXCEPT ![a][r] = v]
    /\ maxBal' = [maxBal EXCEPT ![a] = r]
    /\ UNCHANGED <<proposed, decision, coordVal>>

\* Learn a decision in a classic round when a quorum votes for same value
LearnClassic(r, v) ==
    /\ r \in ClassicRounds
    /\ decision[r] = None
    /\ \E Q \in Quorums : \A a \in Q : votes[a][r] = v
    /\ decision' = [decision EXCEPT ![r] = v]
    /\ UNCHANGED <<proposed, votes, maxBal, coordVal>>

\* Learn a decision in a fast round when a fast quorum votes for same value
LearnFast(r, v) ==
    /\ r \in FastRounds
    /\ decision[r] = None
    /\ \E FQ \in FastQuorums : \A a \in FQ : votes[a][r] = v
    /\ decision' = [decision EXCEPT ![r] = v]
    /\ UNCHANGED <<proposed, votes, maxBal, coordVal>>

\* Coordinator recovers from collision in fast round by starting classic round
\* with value that was voted by intersection of any two fast quorums
RecoverFromCollision(r, v) ==
    /\ r \in FastRounds
    /\ decision[r] = None
    /\ \E FQ1, FQ2 \in FastQuorums :
        LET intersection == FQ1 \cap FQ2
        IN /\ Cardinality(ValuesVotedInRound(r) \cap {votes[a][r] : a \in intersection}) > 0
           /\ \E a \in intersection : votes[a][r] = v
    /\ \E r2 \in ClassicRounds :
        /\ r2 > r
        /\ coordVal[r2] = None
        /\ coordVal' = [coordVal EXCEPT ![r2] = v]
    /\ UNCHANGED <<proposed, votes, maxBal, decision>>

(******************************************************************************)
(* Next-state relation                                                        *)
(******************************************************************************)
Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E r \in ClassicRounds, v \in Values : CoordinatorSelectValue(r, v)
    \/ \E r \in FastRounds : CoordinatorStartFastRound(r)
    \/ \E a \in Acceptors, r \in ClassicRounds, v \in Values : AcceptorVoteClassic(a, r, v)
    \/ \E a \in Acceptors, r \in FastRounds, v \in Values : AcceptorVoteFast(a, r, v)
    \/ \E r \in ClassicRounds, v \in Values : LearnClassic(r, v)
    \/ \E r \in FastRounds, v \in Values : LearnFast(r, v)
    \/ \E r \in FastRounds, v \in Values : RecoverFromCollision(r, v)

(******************************************************************************)
(* Fairness conditions                                                        *)
(******************************************************************************)
Fairness ==
    /\ \A v \in Values : WF_vars(Propose(v))
    /\ \A r \in ClassicRounds, v \in Values : WF_vars(LearnClassic(r, v))
    /\ \A r \in FastRounds, v \in Values : WF_vars(LearnFast(r, v))

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(******************************************************************************)
(* Safety Properties                                                          *)
(******************************************************************************)

\* Non-triviality: Only proposed values can be decided
NonTriviality ==
    \A r \in Rounds : decision[r] # None => decision[r] \in proposed

\* Agreement: At most one value is chosen
Agreement ==
    \A r1, r2 \in Rounds :
        (decision[r1] # None /\ decision[r2] # None) => decision[r1] = decision[r2]

\* Votes are consistent with maxBal
VoteConsistency ==
    \A a \in Acceptors, r \in Rounds :
        votes[a][r] # None => maxBal[a] >= r

(******************************************************************************)
(* Liveness Properties                                                        *)
(******************************************************************************)

\* If a value is proposed, eventually some value is decided
Progress == 
    proposed # {} ~> \E r \in Rounds : decision[r] # None

(******************************************************************************)
(* Invariants for model checking                                              *)
(******************************************************************************)
SafetyInvariant ==
    /\ TypeOK
    /\ NonTriviality
    /\ Agreement

================================================================================
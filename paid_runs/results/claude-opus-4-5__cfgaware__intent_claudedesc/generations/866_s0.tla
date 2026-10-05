---------------------------- MODULE FastPaxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* Set of acceptor replicas
    Values,         \* Set of possible values that can be proposed
    FastBallots,    \* Set of fast ballot numbers
    ClassicBallots  \* Set of classic ballot numbers

VARIABLES
    votes,          \* votes[a] = set of <<ballot, value>> pairs acceptor a has voted for
    maxBal,         \* maxBal[a] = highest ballot acceptor a has participated in
    decision,       \* The decided value (or "none" if no decision yet)
    coordBallot,    \* Current ballot being coordinated
    phase,          \* Current phase: "idle", "fast", "classic1", "classic2"
    proposed,       \* Set of values proposed in current fast round
    fastVotes,      \* fastVotes[v] = set of acceptors that voted for v in current fast round
    classicValue    \* Value selected by coordinator for classic round

vars == <<votes, maxBal, decision, coordBallot, phase, proposed, fastVotes, classicValue>>

None == CHOOSE v : v \notin Values
Ballots == FastBallots \cup ClassicBallots

\* Quorum definitions
\* Fast quorums require at least 3/4 of acceptors
FastQuorum(Q) == 
    /\ Q \subseteq Acceptors
    /\ 4 * Cardinality(Q) > 3 * Cardinality(Acceptors)

\* Classic quorums require a majority
ClassicQuorum(Q) ==
    /\ Q \subseteq Acceptors
    /\ 2 * Cardinality(Q) > Cardinality(Acceptors)

IsFastBallot(b) == b \in FastBallots
IsClassicBallot(b) == b \in ClassicBallots

\* Type invariant
FastTypeOK ==
    /\ votes \in [Acceptors -> SUBSET (Ballots \times Values)]
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ decision \in Values \cup {None}
    /\ coordBallot \in Ballots \cup {-1}
    /\ phase \in {"idle", "fast", "classic1", "classic2"}
    /\ proposed \in SUBSET Values
    /\ fastVotes \in [Values -> SUBSET Acceptors]
    /\ classicValue \in Values \cup {None}

\* Initial state
Init ==
    /\ votes = [a \in Acceptors |-> {}]
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ decision = None
    /\ coordBallot = -1
    /\ phase = "idle"
    /\ proposed = {}
    /\ fastVotes = [v \in Values |-> {}]
    /\ classicValue = None

\* Helper: Get the maximum ballot an acceptor has voted in
MaxVotedBallot(a) ==
    IF votes[a] = {} THEN -1
    ELSE LET ballots == {b : <<b, v>> \in votes[a]}
         IN CHOOSE max \in ballots : \A b \in ballots : b <= max

\* Helper: Get value voted for in a specific ballot by acceptor (if any)
VotedValueInBallot(a, b) ==
    {v \in Values : <<b, v>> \in votes[a]}

\* Helper: Safe to vote - acceptor hasn't promised a higher ballot
SafeToVote(a, b) == maxBal[a] <= b

\* Coordinator starts a fast round
StartFastRound(b) ==
    /\ b \in FastBallots
    /\ phase = "idle"
    /\ coordBallot < b
    /\ coordBallot' = b
    /\ phase' = "fast"
    /\ proposed' = {}
    /\ fastVotes' = [v \in Values |-> {}]
    /\ classicValue' = None
    /\ UNCHANGED <<votes, maxBal, decision>>

\* Acceptor proposes and votes for a value in fast round
FastPropose(a, v) ==
    /\ phase = "fast"
    /\ IsFastBallot(coordBallot)
    /\ SafeToVote(a, coordBallot)
    /\ a \notin UNION {fastVotes[val] : val \in Values}  \* Hasn't voted in this round yet
    \* Consistency check: if voted before, must vote for same value or free to choose
    /\ LET prevBallot == MaxVotedBallot(a)
           prevValues == IF prevBallot = -1 THEN {} 
                        ELSE VotedValueInBallot(a, prevBallot)
       IN prevValues = {} \/ v \in prevValues
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<coordBallot, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = coordBallot]
    /\ proposed' = proposed \cup {v}
    /\ fastVotes' = [fastVotes EXCEPT ![v] = @ \cup {a}]
    /\ UNCHANGED <<decision, coordBallot, phase, classicValue>>

\* Fast decision: fast quorum all voted for same value
FastDecide(v) ==
    /\ phase = "fast"
    /\ decision = None
    /\ FastQuorum(fastVotes[v])
    /\ decision' = v
    /\ phase' = "idle"
    /\ UNCHANGED <<votes, maxBal, coordBallot, proposed, fastVotes, classicValue>>

\* Detect collision in fast round - start classic recovery
DetectCollision ==
    /\ phase = "fast"
    /\ decision = None
    /\ Cardinality(proposed) > 1  \* Multiple values proposed
    \* No single value has a fast quorum
    /\ \A v \in Values : ~FastQuorum(fastVotes[v])
    /\ phase' = "classic1"
    /\ UNCHANGED <<votes, maxBal, decision, coordBallot, proposed, fastVotes, classicValue>>

\* Coordinator selects value for classic round after collision
\* If majority in any fast quorum voted for one value, must select that
\* Otherwise, can select any proposed value
CoordinatorSelectValue ==
    /\ phase = "classic1"
    /\ decision = None
    /\ LET 
         \* Find if any value has majority in a fast quorum
         HasMajorityInFastQuorum(v) ==
           \E Q \in SUBSET Acceptors :
             /\ FastQuorum(Q)
             /\ 2 * Cardinality(fastVotes[v] \cap Q) > Cardinality(Q)
         majorityValues == {v \in proposed : HasMajorityInFastQuorum(v)}
       IN 
         /\ IF majorityValues # {}
            THEN classicValue' \in majorityValues
            ELSE classicValue' \in proposed
    /\ phase' = "classic2"
    /\ UNCHANGED <<votes, maxBal, decision, coordBallot, proposed, fastVotes>>

\* Coordinator starts a classic round (not from collision)
StartClassicRound(b) ==
    /\ b \in ClassicBallots
    /\ phase = "idle"
    /\ coordBallot < b
    /\ coordBallot' = b
    /\ phase' = "classic1"
    /\ proposed' = {}
    /\ fastVotes' = [v \in Values |-> {}]
    /\ classicValue' = None
    /\ UNCHANGED <<votes, maxBal, decision>>

\* In classic round, coordinator proposes any value if no prior votes
CoordinatorProposeClassic(v) ==
    /\ phase = "classic1"
    /\ decision = None
    /\ IsClassicBallot(coordBallot)
    /\ proposed = {}  \* Fresh classic round
    /\ classicValue' = v
    /\ phase' = "classic2"
    /\ UNCHANGED <<votes, maxBal, decision, coordBallot, proposed, fastVotes>>

\* Acceptor votes in classic round
ClassicVote(a) ==
    /\ phase = "classic2"
    /\ classicValue # None
    /\ SafeToVote(a, coordBallot)
    /\ <<coordBallot, classicValue>> \notin votes[a]
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<coordBallot, classicValue>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = coordBallot]
    /\ UNCHANGED <<decision, coordBallot, phase, proposed, fastVotes, classicValue>>

\* Classic decision: classic quorum voted for the value
ClassicDecide ==
    /\ phase = "classic2"
    /\ decision = None
    /\ classicValue # None
    /\ LET voters == {a \in Acceptors : <<coordBallot, classicValue>> \in votes[a]}
       IN ClassicQuorum(voters)
    /\ decision' = classicValue
    /\ phase' = "idle"
    /\ UNCHANGED <<votes, maxBal, coordBallot, proposed, fastVotes, classicValue>>

\* Abort current round and return to idle (modeling timeout/failure)
AbortRound ==
    /\ phase # "idle"
    /\ decision = None
    /\ phase' = "idle"
    /\ UNCHANGED <<votes, maxBal, decision, coordBallot, proposed, fastVotes, classicValue>>

\* Next state relation
Next ==
    \/ \E b \in FastBallots : StartFastRound(b)
    \/ \E a \in Acceptors, v \in Values : FastPropose(a, v)
    \/ \E v \in Values : FastDecide(v)
    \/ DetectCollision
    \/ CoordinatorSelectValue
    \/ \E b \in ClassicBallots : StartClassicRound(b)
    \/ \E v \in Values : CoordinatorProposeClassic(v)
    \/ \E a \in Acceptors : ClassicVote(a)
    \/ ClassicDecide
    \/ AbortRound

\* Fairness conditions for liveness
Fairness ==
    /\ WF_vars(Next)
    /\ \A v \in Values : WF_vars(FastDecide(v))
    /\ WF_vars(ClassicDecide)
    /\ WF_vars(CoordinatorSelectValue)
    /\ \A a \in Acceptors : WF_vars(ClassicVote(a))

\* Main specification
FastSpec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Non-triviality - decided value was proposed
FastNontriviality ==
    decision # None => 
        \E a \in Acceptors, b \in Ballots : <<b, decision>> \in votes[a]

\* Safety: Paxos Consistency - at most one value is decided
\* This is expressed as: once decided, decision doesn't change
PaxosConsistency ==
    [][decision # None => decision' = decision]_vars

=============================================================================
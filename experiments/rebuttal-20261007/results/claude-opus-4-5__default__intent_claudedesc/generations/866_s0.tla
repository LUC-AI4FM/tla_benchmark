--------------------------- MODULE FastPaxos ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,      \* Set of acceptor replicas
    Values,         \* Set of possible values that can be proposed
    Ballots,        \* Set of ballot numbers
    FastBallots,    \* Subset of Ballots that are fast ballots
    ClassicBallots, \* Subset of Ballots that are classic ballots
    FastQuorums,    \* Set of fast quorums
    ClassicQuorums, \* Set of classic quorums
    None            \* A distinguished value representing "no value"

ASSUME FastBallots \subseteq Ballots
ASSUME ClassicBallots \subseteq Ballots
ASSUME FastBallots \intersect ClassicBallots = {}
ASSUME FastBallots \union ClassicBallots = Ballots

\* Quorum assumptions
ASSUME \A Q \in FastQuorums : Q \subseteq Acceptors
ASSUME \A Q \in ClassicQuorums : Q \subseteq Acceptors
ASSUME \A Q1, Q2 \in FastQuorums : Q1 \intersect Q2 /= {}
ASSUME \A Q \in FastQuorums : Cardinality(Q) * 4 >= Cardinality(Acceptors) * 3
ASSUME \A CQ \in ClassicQuorums : \A FQ1, FQ2 \in FastQuorums : 
         CQ \intersect FQ1 \intersect FQ2 /= {}

VARIABLES
    maxBal,         \* maxBal[a] = highest ballot acceptor a has participated in
    maxVBal,        \* maxVBal[a] = ballot number of highest vote cast by acceptor a
    maxVVal,        \* maxVVal[a] = value of highest vote cast by acceptor a
    coordinatorBal, \* Current ballot being coordinated
    fastRoundOpen,  \* fastRoundOpen[b] = TRUE iff fast round b is open for voting
    votes,          \* votes[a] = set of <<ballot, value>> pairs acceptor a has voted for
    proposed,       \* Set of values that have been proposed in fast rounds
    decision        \* The decided value (None if no decision yet)

vars == <<maxBal, maxVBal, maxVVal, coordinatorBal, fastRoundOpen, votes, proposed, decision>>

TypeOK ==
    /\ maxBal \in [Acceptors -> Ballots \union {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \union {-1}]
    /\ maxVVal \in [Acceptors -> Values \union {None}]
    /\ coordinatorBal \in Ballots \union {-1}
    /\ fastRoundOpen \in [FastBallots -> BOOLEAN]
    /\ votes \in [Acceptors -> SUBSET (Ballots \times Values)]
    /\ proposed \in SUBSET Values
    /\ decision \in Values \union {None}

Init ==
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVVal = [a \in Acceptors |-> None]
    /\ coordinatorBal = -1
    /\ fastRoundOpen = [b \in FastBallots |-> FALSE]
    /\ votes = [a \in Acceptors |-> {}]
    /\ proposed = {}
    /\ decision = None

\* Helper: Get votes in a specific ballot
VotesInBallot(b) == {<<a, v>> : a \in Acceptors, v \in Values : <<b, v>> \in votes[a]}

\* Helper: Get the set of values voted for in ballot b
ValuesVotedInBallot(b) == {v \in Values : \E a \in Acceptors : <<b, v>> \in votes[a]}

\* Helper: Count votes for value v in ballot b within a quorum Q
VoteCount(b, v, Q) == Cardinality({a \in Q : <<b, v>> \in votes[a]})

\* Helper: Check if value v is safe to vote for in ballot b
\* A value is safe if no other value could have been chosen in any earlier ballot
SafeAt(v, b) ==
    \A c \in Ballots : c < b =>
        \/ \A a \in Acceptors : maxVBal[a] /= c
        \/ \E Q \in ClassicQuorums : 
             \A a \in Q : maxBal[a] >= b \/ (maxVBal[a] = c => maxVVal[a] = v)

\* Coordinator starts a fast round
StartFastRound(b) ==
    /\ b \in FastBallots
    /\ b > coordinatorBal
    /\ coordinatorBal' = b
    /\ fastRoundOpen' = [fastRoundOpen EXCEPT ![b] = TRUE]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, votes, proposed, decision>>

\* Acceptor proposes and votes in a fast round
FastVote(a, b, v) ==
    /\ b \in FastBallots
    /\ fastRoundOpen[b] = TRUE
    /\ maxBal[a] <= b
    /\ \/ maxVBal[a] = -1  \* No previous vote
       \/ maxVVal[a] = v   \* Consistent with previous vote
       \/ maxVBal[a] < b   \* Can vote for any value in higher ballot
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVVal' = [maxVVal EXCEPT ![a] = v]
    /\ votes' = [votes EXCEPT ![a] = @ \union {<<b, v>>}]
    /\ proposed' = proposed \union {v}
    /\ UNCHANGED <<coordinatorBal, fastRoundOpen, decision>>

\* Fast decision: A fast quorum agrees on a value
FastDecide(b, v) ==
    /\ b \in FastBallots
    /\ decision = None
    /\ \E Q \in FastQuorums : \A a \in Q : <<b, v>> \in votes[a]
    /\ decision' = v
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, coordinatorBal, fastRoundOpen, votes, proposed>>

\* Coordinator detects collision and starts classic round
\* Returns the value to propose based on collision recovery rules
PickValueForClassicRound(b) ==
    LET 
        prevFastBallots == {fb \in FastBallots : fb < b}
        \* Find if any value has majority in a fast quorum from previous fast ballot
        MajorityValue == 
            {v \in Values : 
                \E fb \in prevFastBallots :
                \E Q \in FastQuorums :
                    VoteCount(fb, v, Q) * 2 > Cardinality(Q)}
    IN
        IF MajorityValue /= {} 
        THEN CHOOSE v \in MajorityValue : TRUE
        ELSE IF proposed /= {} 
             THEN CHOOSE v \in proposed : TRUE
             ELSE None

\* Coordinator starts a classic round to resolve collision
StartClassicRound(b) ==
    /\ b \in ClassicBallots
    /\ b > coordinatorBal
    /\ coordinatorBal' = b
    \* Close any open fast rounds with lower ballots
    /\ fastRoundOpen' = [fb \in FastBallots |-> 
                          IF fb < b THEN FALSE ELSE fastRoundOpen[fb]]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, votes, proposed, decision>>

\* Phase 1a: Coordinator sends prepare for classic round (implicit in StartClassicRound)

\* Phase 1b: Acceptor responds to prepare
Phase1b(a, b) ==
    /\ b \in ClassicBallots
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED <<maxVBal, maxVVal, coordinatorBal, fastRoundOpen, votes, proposed, decision>>

\* Phase 2a: Coordinator picks value based on Phase 1b responses
\* The coordinator selects a value based on the highest ballot vote seen
PickValue(b) ==
    LET 
        \* Get the highest ballot at which any acceptor in a quorum voted
        HighestVoteBallot(Q) == 
            LET ballots == {maxVBal[a] : a \in Q}
            IN IF ballots = {-1} THEN -1 
               ELSE CHOOSE m \in ballots : \A x \in ballots : x <= m
        \* Get the value(s) voted at the highest ballot
        HighestVoteValue(Q) ==
            LET hb == HighestVoteBallot(Q)
            IN IF hb = -1 THEN Values
               ELSE {maxVVal[a] : a \in Q : maxVBal[a] = hb}
    IN
        \E Q \in ClassicQuorums :
            /\ \A a \in Q : maxBal[a] >= b
            /\ LET hvv == HighestVoteValue(Q)
               IN IF hvv \subseteq {None} 
                  THEN PickValueForClassicRound(b)
                  ELSE CHOOSE v \in (hvv \ {None}) : TRUE

\* Phase 2b: Acceptor votes in classic round
ClassicVote(a, b, v) ==
    /\ b \in ClassicBallots
    /\ b >= maxBal[a]
    /\ v \in Values
    /\ SafeAt(v, b)
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVVal' = [maxVVal EXCEPT ![a] = v]
    /\ votes' = [votes EXCEPT ![a] = @ \union {<<b, v>>}]
    /\ UNCHANGED <<coordinatorBal, fastRoundOpen, proposed, decision>>

\* Classic decision: A classic quorum agrees on a value
ClassicDecide(b, v) ==
    /\ b \in ClassicBallots
    /\ decision = None
    /\ \E Q \in ClassicQuorums : \A a \in Q : <<b, v>> \in votes[a]
    /\ decision' = v
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, coordinatorBal, fastRoundOpen, votes, proposed>>

\* Next state relation
Next ==
    \/ \E b \in FastBallots : StartFastRound(b)
    \/ \E a \in Acceptors, b \in FastBallots, v \in Values : FastVote(a, b, v)
    \/ \E b \in FastBallots, v \in Values : FastDecide(b, v)
    \/ \E b \in ClassicBallots : StartClassicRound(b)
    \/ \E a \in Acceptors, b \in ClassicBallots : Phase1b(a, b)
    \/ \E a \in Acceptors, b \in ClassicBallots, v \in Values : ClassicVote(a, b, v)
    \/ \E b \in ClassicBallots, v \in Values : ClassicDecide(b, v)

\* Fairness conditions
Fairness ==
    /\ \A b \in FastBallots : WF_vars(StartFastRound(b))
    /\ \A a \in Acceptors, b \in FastBallots, v \in Values : WF_vars(FastVote(a, b, v))
    /\ \A b \in FastBallots, v \in Values : WF_vars(FastDecide(b, v))
    /\ \A b \in ClassicBallots : WF_vars(StartClassicRound(b))
    /\ \A a \in Acceptors, b \in ClassicBallots : WF_vars(Phase1b(a, b))
    /\ \A a \in Acceptors, b \in ClassicBallots, v \in Values : WF_vars(ClassicVote(a, b, v))
    /\ \A b \in ClassicBallots, v \in Values : WF_vars(ClassicDecide(b, v))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================
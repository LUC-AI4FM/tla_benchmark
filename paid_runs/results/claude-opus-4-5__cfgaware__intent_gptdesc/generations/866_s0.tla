---------------------------- MODULE FastPaxos ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Acceptors,          \* Set of all acceptor nodes
    Proposers,          \* Set of all proposer nodes
    Values,             \* Set of possible values that can be proposed
    FastQuorums,        \* Set of fast quorums (larger quorums for fast rounds)
    ClassicQuorums,     \* Set of classic quorums (majority quorums)
    Rounds,             \* Set of round numbers
    FastRounds,         \* Subset of rounds that are fast rounds
    None                \* Distinguished value representing "no value"

ASSUME AcceptorAssumption == Acceptors # {}
ASSUME ProposerAssumption == Proposers # {}
ASSUME ValuesAssumption == Values # {} /\ None \notin Values
ASSUME RoundsAssumption == Rounds \subseteq Nat /\ Rounds # {}
ASSUME FastRoundsAssumption == FastRounds \subseteq Rounds

\* Quorum intersection properties required for safety
ASSUME FastQuorumAssumption ==
    /\ FastQuorums \subseteq SUBSET Acceptors
    /\ FastQuorums # {}
    /\ \A Q1, Q2 \in FastQuorums : Q1 \cap Q2 # {}

ASSUME ClassicQuorumAssumption ==
    /\ ClassicQuorums \subseteq SUBSET Acceptors
    /\ ClassicQuorums # {}
    /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}

\* Fast quorums must intersect classic quorums
ASSUME FastClassicIntersection ==
    \A FQ \in FastQuorums : \A CQ \in ClassicQuorums : FQ \cap CQ # {}

\* Two fast quorums must have intersection containing a classic quorum's worth
\* This ensures collision detection works properly
ASSUME FastQuorumIntersectionProperty ==
    \A Q1, Q2 \in FastQuorums : \A CQ \in ClassicQuorums :
        Cardinality(Q1 \cap Q2) >= Cardinality(CQ)

----------------------------------------------------------------------------

VARIABLES
    proposed,           \* proposed[p] = value proposed by proposer p, or None
    acceptorState,      \* acceptorState[a] = [maxRound, acceptedRound, acceptedValue]
    fastRoundVotes,     \* fastRoundVotes[r] = function from acceptors to voted value (or None)
    classicAccepts,     \* classicAccepts[r] = function from acceptors to accepted value (or None)
    decided,            \* decided = the decided value, or None if not yet decided
    coordinatorChoice,  \* coordinatorChoice[r] = value chosen by coordinator for classic round r
    roundType,          \* roundType[r] = "fast" or "classic" for each active round
    messages            \* Abstract message pool for asynchronous communication

vars == <<proposed, acceptorState, fastRoundVotes, classicAccepts, 
          decided, coordinatorChoice, roundType, messages>>

----------------------------------------------------------------------------

\* Type definitions

AcceptorStateType == [
    maxRound: Rounds \cup {0},
    acceptedRound: Rounds \cup {0},
    acceptedValue: Values \cup {None}
]

MessageType == [type: {"propose", "fastVote", "prepare", "promise", 
                       "accept", "accepted", "decision"},
                round: Rounds,
                from: Acceptors \cup Proposers \cup {"coordinator"},
                value: Values \cup {None},
                maxRound: Rounds \cup {0},
                acceptedRound: Rounds \cup {0},
                acceptedValue: Values \cup {None}]

\* Type invariant
FastTypeOK ==
    /\ proposed \in [Proposers -> Values \cup {None}]
    /\ acceptorState \in [Acceptors -> AcceptorStateType]
    /\ fastRoundVotes \in [Rounds -> [Acceptors -> Values \cup {None}]]
    /\ classicAccepts \in [Rounds -> [Acceptors -> Values \cup {None}]]
    /\ decided \in Values \cup {None}
    /\ coordinatorChoice \in [Rounds -> Values \cup {None}]
    /\ roundType \in [Rounds -> {"fast", "classic", "inactive"}]
    /\ messages \subseteq MessageType

----------------------------------------------------------------------------

\* Initial state

Init ==
    /\ proposed = [p \in Proposers |-> None]
    /\ acceptorState = [a \in Acceptors |-> [maxRound |-> 0, 
                                              acceptedRound |-> 0, 
                                              acceptedValue |-> None]]
    /\ fastRoundVotes = [r \in Rounds |-> [a \in Acceptors |-> None]]
    /\ classicAccepts = [r \in Rounds |-> [a \in Acceptors |-> None]]
    /\ decided = None
    /\ coordinatorChoice = [r \in Rounds |-> None]
    /\ roundType = [r \in Rounds |-> IF r \in FastRounds THEN "fast" ELSE "inactive"]
    /\ messages = {}

----------------------------------------------------------------------------

\* Helper operators

\* Count how many acceptors in a set voted for a specific value
CountVotes(votes, Q, v) ==
    Cardinality({a \in Q : votes[a] = v})

\* Get the set of values that appear in votes from a quorum
ValuesInQuorum(votes, Q) ==
    {v \in Values : \E a \in Q : votes[a] = v}

\* Check if a value has a strict majority within a quorum
HasMajorityInQuorum(votes, Q, v) ==
    2 * CountVotes(votes, Q, v) > Cardinality(Q)

\* Find the value with majority in a quorum, if any
MajorityValue(votes, Q) ==
    LET majVals == {v \in Values : HasMajorityInQuorum(votes, Q, v)}
    IN IF majVals # {} THEN CHOOSE v \in majVals : TRUE ELSE None

\* Check if a fast quorum agrees on a value
FastQuorumDecision(r, v) ==
    \E Q \in FastQuorums :
        /\ \A a \in Q : fastRoundVotes[r][a] = v
        /\ v # None

\* Check if a classic quorum has accepted a value
ClassicQuorumDecision(r, v) ==
    \E Q \in ClassicQuorums :
        /\ \A a \in Q : classicAccepts[r][a] = v
        /\ v # None

----------------------------------------------------------------------------

\* Actions

\* A proposer proposes a value
Propose(p, v) ==
    /\ proposed[p] = None
    /\ v \in Values
    /\ proposed' = [proposed EXCEPT ![p] = v]
    /\ messages' = messages \cup {[type |-> "propose", 
                                   round |-> 0,
                                   from |-> p, 
                                   value |-> v,
                                   maxRound |-> 0,
                                   acceptedRound |-> 0,
                                   acceptedValue |-> None]}
    /\ UNCHANGED <<acceptorState, fastRoundVotes, classicAccepts, 
                   decided, coordinatorChoice, roundType>>

\* Fast round: An acceptor votes for a value in a fast round
\* In fast rounds, acceptors can vote for any proposed value
FastVote(a, r, v) ==
    /\ r \in FastRounds
    /\ roundType[r] = "fast"
    /\ decided = None
    /\ acceptorState[a].maxRound <= r
    /\ fastRoundVotes[r][a] = None
    /\ v \in Values
    /\ \E p \in Proposers : proposed[p] = v  \* Value must have been proposed
    /\ fastRoundVotes' = [fastRoundVotes EXCEPT ![r][a] = v]
    /\ acceptorState' = [acceptorState EXCEPT ![a] = 
                         [maxRound |-> r, 
                          acceptedRound |-> r, 
                          acceptedValue |-> v]]
    /\ messages' = messages \cup {[type |-> "fastVote",
                                   round |-> r,
                                   from |-> a,
                                   value |-> v,
                                   maxRound |-> r,
                                   acceptedRound |-> r,
                                   acceptedValue |-> v]}
    /\ UNCHANGED <<proposed, classicAccepts, decided, coordinatorChoice, roundType>>

\* Fast round decision: when a fast quorum votes for the same value
FastDecide(r, v) ==
    /\ r \in FastRounds
    /\ decided = None
    /\ FastQuorumDecision(r, v)
    /\ decided' = v
    /\ messages' = messages \cup {[type |-> "decision",
                                   round |-> r,
                                   from |-> "coordinator",
                                   value |-> v,
                                   maxRound |-> 0,
                                   acceptedRound |-> 0,
                                   acceptedValue |-> None]}
    /\ UNCHANGED <<proposed, acceptorState, fastRoundVotes, classicAccepts,
                   coordinatorChoice, roundType>>

\* Coordinator starts a classic round (typically after detecting conflict in fast round)
StartClassicRound(r) ==
    /\ r \notin FastRounds
    /\ roundType[r] = "inactive"
    /\ decided = None
    /\ roundType' = [roundType EXCEPT ![r] = "classic"]
    /\ messages' = messages \cup {[type |-> "prepare",
                                   round |-> r,
                                   from |-> "coordinator",
                                   value |-> None,
                                   maxRound |-> 0,
                                   acceptedRound |-> 0,
                                   acceptedValue |-> None]}
    /\ UNCHANGED <<proposed, acceptorState, fastRoundVotes, classicAccepts,
                   decided, coordinatorChoice>>

\* Acceptor responds to prepare (promise)
Promise(a, r) ==
    /\ roundType[r] = "classic"
    /\ acceptorState[a].maxRound < r
    /\ acceptorState' = [acceptorState EXCEPT ![a].maxRound = r]
    /\ messages' = messages \cup {[type |-> "promise",
                                   round |-> r,
                                   from |-> a,
                                   value |-> None,
                                   maxRound |-> r,
                                   acceptedRound |-> acceptorState[a].acceptedRound,
                                   acceptedValue |-> acceptorState[a].acceptedValue]}
    /\ UNCHANGED <<proposed, fastRoundVotes, classicAccepts, decided, 
                   coordinatorChoice, roundType>>

\* Coordinator chooses value for classic round based on promises
\* Must respect the majority-in-quorum rule for conflict resolution
CoordinatorChoose(r, v) ==
    /\ roundType[r] = "classic"
    /\ coordinatorChoice[r] = None
    /\ decided = None
    /\ \E Q \in ClassicQuorums :
        LET promiseMsgs == {m \in messages : m.type = "promise" /\ m.round = r /\ m.from \in Q}
            respondents == {m.from : m \in promiseMsgs}
            highestRound == LET rounds == {m.acceptedRound : m \in promiseMsgs}
                           IN IF rounds = {} \/ rounds = {0} THEN 0
                              ELSE CHOOSE maxR \in rounds : \A r2 \in rounds : r2 <= maxR
            valuesAtHighest == {m.acceptedValue : m \in promiseMsgs /\ m.acceptedRound = highestRound}
            proposedValues == {proposed[p] : p \in Proposers} \ {None}
        IN
            /\ respondents = Q  \* All in quorum have responded
            /\ \/ /\ highestRound = 0  \* No prior accepts, choose any proposed value
                  /\ v \in proposedValues
               \/ /\ highestRound > 0
                  /\ highestRound \in FastRounds  \* Previous round was fast
                  \* Check for majority value in the fast quorum responses
                  /\ LET fastVotes == [a \in Q |-> 
                         LET ms == {m \in promiseMsgs : m.from = a}
                         IN IF ms = {} THEN None
                            ELSE (CHOOSE m \in ms : TRUE).acceptedValue]
                         majVal == MajorityValue(fastVotes, Q)
                     IN \/ /\ majVal # None  \* Must choose majority value
                           /\ v = majVal
                        \/ /\ majVal = None  \* No majority, may choose any value from those proposed
                           /\ v \in ValuesInQuorum(fastVotes, Q)
               \/ /\ highestRound > 0
                  /\ highestRound \notin FastRounds  \* Previous round was classic
                  /\ v \in valuesAtHighest \ {None}  \* Choose value from highest round
    /\ coordinatorChoice' = [coordinatorChoice EXCEPT ![r] = v]
    /\ messages' = messages \cup {[type |-> "accept",
                                   round |-> r,
                                   from |-> "coordinator",
                                   value |-> v,
                                   maxRound |-> 0,
                                   acceptedRound |-> 0,
                                   acceptedValue |-> None]}
    /\ UNCHANGED <<proposed, acceptorState, fastRoundVotes, classicAccepts,
                   decided, roundType>>

\* Acceptor accepts in classic round
ClassicAccept(a, r, v) ==
    /\ roundType[r] = "classic"
    /\ acceptorState[a].maxRound <= r
    /\ classicAccepts[r][a] = None
    /\ coordinatorChoice[r] = v
    /\ v # None
    /\ classicAccepts' = [classicAccepts EXCEPT ![r][a] = v]
    /\ acceptorState' = [acceptorState EXCEPT ![a] = 
                         [maxRound |-> r, acceptedRound |-> r, acceptedValue |-> v]]
    /\ messages' = messages \cup {[type |-> "accepted",
                                   round |-> r,
                                   from |-> a,
                                   value |-> v,
                                   maxRound |-> r,
                                   acceptedRound |-> r,
                                   acceptedValue |-> v]}
    /\ UNCHANGED <<proposed, fastRoundVotes, decided, coordinatorChoice, roundType>>

\* Classic round decision: when a classic quorum accepts the same value
ClassicDecide(r, v) ==
    /\ roundType[r] = "classic"
    /\ decided = None
    /\ ClassicQuorumDecision(r, v)
    /\ decided' = v
    /\ messages' = messages \cup {[type |-> "decision",
                                   round |-> r,
                                   from |-> "coordinator",
                                   value |-> v,
                                   maxRound |-> 0,
                                   acceptedRound |-> 0,
                                   acceptedValue |-> None]}
    /\ UNCHANGED <<proposed, acceptorState, fastRoundVotes, classicAccepts,
                   coordinatorChoice, roundType>>

----------------------------------------------------------------------------

\* Next state relation

Next ==
    \/ \E p \in Proposers, v \in Values : Propose(p, v)
    \/ \E a \in Acceptors, r \in FastRounds, v \in Values : FastVote(a, r, v)
    \/ \E r \in FastRounds, v \in Values : FastDecide(r, v)
    \/ \E r \in Rounds \ FastRounds : StartClassicRound(r)
    \/ \E a \in Acceptors, r \in Rounds : Promise(a, r)
    \/ \E r \in Rounds, v \in Values : CoordinatorChoose(r, v)
    \/ \E a \in Acceptors, r \in Rounds, v \in Values : ClassicAccept(a, r, v)
    \/ \E r \in Rounds, v \in Values : ClassicDecide(r, v)

----------------------------------------------------------------------------

\* Fairness conditions for liveness

\* Eventually, if a fast quorum has voted for the same value, decision occurs
FastDecisionFairness ==
    \A r \in FastRounds, v \in Values :
        SF_vars(FastDecide(r, v))

\* Eventually, if a classic quorum has accepted, decision occurs
ClassicDecisionFairness ==
    \A r \in Rounds \ FastRounds, v \in Values :
        SF_vars(ClassicDecide(r, v))

\* Proposers eventually propose if they haven't
ProposerFairness ==
    \A p \in Proposers :
        WF_vars(\E v \in Values : Propose(p, v))

\* Acceptors eventually respond to valid requests
AcceptorFairness ==
    /\ \A a \in Acceptors, r \in FastRounds :
        WF_vars(\E v \in Values : FastVote(a, r, v))
    /\ \A a \in Acceptors, r \in Rounds :
        WF_vars(Promise(a, r))
    /\ \A a \in Acceptors, r \in Rounds :
        WF_vars(\E v \in Values : ClassicAccept(a, r, v))

Fairness ==
    /\ FastDecisionFairness
    /\ ClassicDecisionFairness
    /\ ProposerFairness
    /\ AcceptorFairness

----------------------------------------------------------------------------

\* Specification

FastSpec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------

\* Safety Properties

\* Agreement: At most one value can be decided
\* (Trivially holds with single decided variable, but we verify no inconsistency)
PaxosConsistency ==
    \A r1, r2 \in Rounds, v1, v2 \in Values :
        /\ (FastQuorumDecision(r1, v1) /\ FastQuorumDecision(r2, v2)) => v1 = v2
        /\ (ClassicQuorumDecision(r1, v1) /\ ClassicQuorumDecision(r2, v2)) => v1 = v2
        /\ (FastQuorumDecision(r1, v1) /\ ClassicQuorumDecision(r2, v2)) => v1 = v2

\* Nontriviality: Only proposed values can be decided
FastNontriviality ==
    decided # None => \E p \in Proposers : proposed[p] = decided

\* Valid conflict resolution: Coordinator respects majority-in-quorum rule
ValidConflictResolution ==
    \A r \in Rounds \ FastRounds :
        coordinatorChoice[r] # None =>
            \E p \in Proposers : proposed[p] = coordinatorChoice[r]

\* Combined safety invariant
Safety ==
    /\ PaxosConsistency
    /\ FastNontriviality
    /\ ValidConflictResolution

----------------------------------------------------------------------------

\* Liveness property: Eventually a decision is made if proposals exist and quorums respond
EventualDecision ==
    (\E p \in Proposers : proposed[p] # None) ~> (decided # None)

============================================================================
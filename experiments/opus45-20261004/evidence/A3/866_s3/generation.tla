------------------------------ MODULE FastPaxos ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    Acceptors,      \* Set of acceptor agents
    Proposers,      \* Set of proposer agents  
    Values,         \* Set of proposable values
    FastQuorums,    \* Set of fast quorums
    ClassicQuorums, \* Set of classic quorums
    Coordinator     \* The unique coordinator

VARIABLES
    proposed,       \* Set of values that have been proposed
    votes,          \* votes[a][r] = value voted by acceptor a in round r (or None)
    maxRound,       \* maxRound[a] = highest round acceptor a has participated in
    decision,       \* The decided value (or None if no decision yet)
    cValue,         \* Coordinator's current value
    messages        \* Set of messages in transit

None == CHOOSE v : v \notin Values

Rounds == 0..10  \* Bounded set of rounds for model checking

Message ==
    [type : {"1a"}, round : Rounds]
    \cup [type : {"1b"}, round : Rounds, acc : Acceptors, 
          maxVRound : Rounds \cup {-1}, maxVVal : Values \cup {None}]
    \cup [type : {"2a"}, round : Rounds, value : Values]
    \cup [type : {"2b"}, round : Rounds, acc : Acceptors, value : Values]
    \cup [type : {"propose"}, value : Values]

vars == <<proposed, votes, maxRound, decision, cValue, messages>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ votes \in [Acceptors -> [Rounds -> Values \cup {None}]]
    /\ maxRound \in [Acceptors -> Rounds \cup {-1}]
    /\ decision \in Values \cup {None}
    /\ cValue \in Values \cup {None}
    /\ messages \subseteq Message

\* Quorum intersection properties
FastQuorumAssumption == 
    \A Q1, Q2 \in FastQuorums : Q1 \cap Q2 # {}
    
ClassicQuorumAssumption ==
    \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}
    
FastClassicQuorumAssumption ==
    \A FQ \in FastQuorums : \A CQ1, CQ2 \in ClassicQuorums :
        FQ \cap CQ1 \cap CQ2 # {}

IsFastRound(r) == r % 2 = 0
IsClassicRound(r) == r % 2 = 1

Init ==
    /\ proposed = {}
    /\ votes = [a \in Acceptors |-> [r \in Rounds |-> None]]
    /\ maxRound = [a \in Acceptors |-> -1]
    /\ decision = None
    /\ cValue = None
    /\ messages = {}

\* A proposer proposes a value
Propose(v) ==
    /\ v \in Values
    /\ proposed' = proposed \cup {v}
    /\ messages' = messages \cup {[type |-> "propose", value |-> v]}
    /\ UNCHANGED <<votes, maxRound, decision, cValue>>

\* Coordinator starts a round by sending 1a message
Phase1a(r) ==
    /\ r \in Rounds
    /\ messages' = messages \cup {[type |-> "1a", round |-> r]}
    /\ UNCHANGED <<proposed, votes, maxRound, decision, cValue>>

\* Acceptor responds to 1a with 1b message
Phase1b(a, r) ==
    /\ [type |-> "1a", round |-> r] \in messages
    /\ maxRound[a] < r
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ LET maxVotedRound == 
            CHOOSE mr \in Rounds \cup {-1} :
                /\ (mr = -1 \/ votes[a][mr] # None)
                /\ \A r2 \in Rounds : r2 > mr => votes[a][r2] = None
       IN messages' = messages \cup 
            {[type |-> "1b", 
              round |-> r, 
              acc |-> a,
              maxVRound |-> maxVotedRound,
              maxVVal |-> IF maxVotedRound = -1 THEN None ELSE votes[a][maxVotedRound]]}
    /\ UNCHANGED <<proposed, votes, decision, cValue>>

\* Get the set of 1b messages for a given round
Msgs1b(r) == {m \in messages : m.type = "1b" /\ m.round = r}

\* Get the highest round from a set of 1b messages where a vote was cast
HighestVotedRound(msgs) ==
    LET rounds == {m.maxVRound : m \in msgs}
    IN IF rounds = {-1} THEN -1
       ELSE CHOOSE r \in rounds : r # -1 /\ \A r2 \in rounds : r2 <= r

\* Values voted in the highest round from a set of 1b messages
ValuesInHighestRound(msgs) ==
    LET hr == HighestVotedRound(msgs)
    IN IF hr = -1 THEN {}
       ELSE {m.maxVVal : m \in {m2 \in msgs : m2.maxVRound = hr}}

\* Coordinator picks a value based on 1b messages (classic round)
CoordinatorPickValue(r) ==
    /\ IsClassicRound(r)
    /\ \E Q \in ClassicQuorums :
        /\ \A a \in Q : \E m \in Msgs1b(r) : m.acc = a
        /\ LET msgs == {m \in Msgs1b(r) : m.acc \in Q}
               vals == ValuesInHighestRound(msgs)
           IN /\ cValue' = IF vals = {} 
                           THEN CHOOSE v \in Values : 
                                    [type |-> "propose", value |-> v] \in messages
                           ELSE IF Cardinality(vals) = 1
                           THEN CHOOSE v \in vals : TRUE
                           ELSE CHOOSE v \in vals : TRUE  \* Any value from collision
              /\ messages' = messages \cup 
                    {[type |-> "2a", round |-> r, value |-> cValue']}
    /\ UNCHANGED <<proposed, votes, maxRound, decision>>

\* Fast round - proposers can directly send 2a
FastPropose(r, v) ==
    /\ IsFastRound(r)
    /\ [type |-> "propose", value |-> v] \in messages
    /\ ~\E m \in messages : m.type = "2a" /\ m.round = r
    /\ messages' = messages \cup {[type |-> "2a", round |-> r, value |-> v]}
    /\ UNCHANGED <<proposed, votes, maxRound, decision, cValue>>

\* Acceptor votes in Phase 2b
Phase2b(a, r) ==
    /\ \E m \in messages :
        /\ m.type = "2a"
        /\ m.round = r
        /\ maxRound[a] <= r
        /\ votes[a][r] = None
        /\ votes' = [votes EXCEPT ![a][r] = m.value]
        /\ maxRound' = [maxRound EXCEPT ![a] = r]
        /\ messages' = messages \cup 
              {[type |-> "2b", round |-> r, acc |-> a, value |-> m.value]}
    /\ UNCHANGED <<proposed, decision, cValue>>

\* Get 2b messages for a round
Msgs2b(r) == {m \in messages : m.type = "2b" /\ m.round = r}

\* Learn a decided value from fast quorum
LearnFast(r, v) ==
    /\ IsFastRound(r)
    /\ decision = None
    /\ \E Q \in FastQuorums :
        /\ \A a \in Q : \E m \in Msgs2b(r) : m.acc = a /\ m.value = v
    /\ decision' = v
    /\ UNCHANGED <<proposed, votes, maxRound, cValue, messages>>

\* Learn a decided value from classic quorum  
LearnClassic(r, v) ==
    /\ IsClassicRound(r)
    /\ decision = None
    /\ \E Q \in ClassicQuorums :
        /\ \A a \in Q : \E m \in Msgs2b(r) : m.acc = a /\ m.value = v
    /\ decision' = v
    /\ UNCHANGED <<proposed, votes, maxRound, cValue, messages>>

\* Collision recovery - coordinator starts a new classic round after collision
CollisionRecovery(r) ==
    /\ IsFastRound(r)
    /\ r + 1 \in Rounds
    /\ \E Q \in FastQuorums :
        LET msgs == {m \in Msgs2b(r) : m.acc \in Q}
            vals == {m.value : m \in msgs}
        IN /\ Cardinality(vals) > 1  \* Collision detected
           /\ messages' = messages \cup {[type |-> "1a", round |-> r + 1]}
    /\ UNCHANGED <<proposed, votes, maxRound, decision, cValue>>

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E r \in Rounds : Phase1a(r)
    \/ \E a \in Acceptors, r \in Rounds : Phase1b(a, r)
    \/ \E r \in Rounds : CoordinatorPickValue(r)
    \/ \E r \in Rounds, v \in Values : FastPropose(r, v)
    \/ \E a \in Acceptors, r \in Rounds : Phase2b(a, r)
    \/ \E r \in Rounds, v \in Values : LearnFast(r, v)
    \/ \E r \in Rounds, v \in Values : LearnClassic(r, v)
    \/ \E r \in Rounds : CollisionRecovery(r)

Spec == Init /\ [][Next]_vars

\* Safety: Non-triviality - only proposed values can be decided
NonTriviality == decision # None => decision \in proposed

\* Safety: Agreement - at most one value is decided
Agreement == 
    \A v1, v2 \in Values : 
        (decision = v1 /\ decision = v2) => v1 = v2

\* Safety: Votes are consistent within a round
VoteConsistency ==
    \A a \in Acceptors, r \in Rounds :
        votes[a][r] # None => 
            \E m \in messages : m.type = "2a" /\ m.round = r /\ m.value = votes[a][r]

\* Combined safety invariant
SafetyInvariant == 
    /\ TypeOK
    /\ NonTriviality
    /\ Agreement

\* Liveness: Eventually a decision is made (requires fairness)
Liveness == <>(decision # None)

\* Fairness condition
FairSpec == Spec /\ WF_vars(Next)

=============================================================================
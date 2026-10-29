---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ IsFiniteSet(Replicas)
       /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Slots)
       /\ Ballots \subseteq Nat

VARIABLES msgs,      \* set of all messages ever sent
          lBallot,   \* lBallot[r]: ballot replica r is leading with (NullBallot if none)
          lStatus,   \* lStatus[r]: leader status of replica r
          rBallot,   \* rBallot[r]: highest ballot promised by acceptor r
          rVoted,    \* rVoted[r][s]: highest-balloted vote of acceptor r in slot s
          proposed,  \* set of <<slot, value>> pairs ever proposed
          learned    \* learned[r][s]: value learned by replica r for slot s

vars == <<msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned>>

NullBallot == -1
NullValue  == CHOOSE v : v \notin Values

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

NullVote == [bal |-> NullBallot, val |-> NullValue]

Votes == [bal : Ballots \cup {NullBallot}, val : Values \cup {NullValue}]

PrepareMsgs      == [type : {"Prepare"}, src : Replicas, bal : Ballots]
PrepareReplyMsgs == [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
                     voted : [Slots -> Votes]]
AcceptMsgs       == [type : {"Accept"}, src : Replicas, bal : Ballots,
                     slot : Slots, val : Values]
AcceptReplyMsgs  == [type : {"AcceptReply"}, src : Replicas, bal : Ballots,
                     slot : Slots, val : Values]

Messages == PrepareMsgs \cup PrepareReplyMsgs \cup AcceptMsgs \cup AcceptReplyMsgs

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \subseteq Messages
    /\ lBallot \in [Replicas -> Ballots \cup {NullBallot}]
    /\ lStatus \in [Replicas -> {"Idle", "Preparing", "Leading"}]
    /\ rBallot \in [Replicas -> Ballots \cup {NullBallot}]
    /\ rVoted \in [Replicas -> [Slots -> Votes]]
    /\ proposed \subseteq (Slots \X Values)
    /\ learned \in [Replicas -> [Slots -> Values \cup {NullValue}]]

Init ==
    /\ msgs = {}
    /\ lBallot = [r \in Replicas |-> NullBallot]
    /\ lStatus = [r \in Replicas |-> "Idle"]
    /\ rBallot = [r \in Replicas |-> NullBallot]
    /\ rVoted = [r \in Replicas |-> [s \in Slots |-> NullVote]]
    /\ proposed = {}
    /\ learned = [r \in Replicas |-> [s \in Slots |-> NullValue]]

-----------------------------------------------------------------------------
\* A replica starts a prepare phase (covering all slots) with a fresh, unique ballot.
Prepare(r, b) ==
    /\ b > lBallot[r]
    /\ b > rBallot[r]
    /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ lBallot' = [lBallot EXCEPT ![r] = b]
    /\ lStatus' = [lStatus EXCEPT ![r] = "Preparing"]
    /\ Send([type |-> "Prepare", src |-> r, bal |-> b])
    /\ UNCHANGED <<rBallot, rVoted, proposed, learned>>

\* An acceptor handles a prepare and replies with its full voting history.
HandlePrepare(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ Send([type |-> "PrepareReply", src |-> r, bal |-> m.bal,
                 voted |-> rVoted[r]])
        /\ UNCHANGED <<lBallot, lStatus, rVoted, proposed, learned>>

PrepareRepliesFrom(Q, b) ==
    {m \in msgs : m.type = "PrepareReply" /\ m.bal = b /\ m.src \in Q}

HasPrepareQuorum(Q, b) ==
    \A q \in Q : \E m \in msgs : m.type = "PrepareReply" /\ m.bal = b /\ m.src = q

\* A replica becomes leader once a majority has acknowledged its prepare.
BecomeLeader(r) ==
    /\ lStatus[r] = "Preparing"
    /\ \E Q \in Quorums : HasPrepareQuorum(Q, lBallot[r])
    /\ lStatus' = [lStatus EXCEPT ![r] = "Leading"]
    /\ UNCHANGED <<msgs, lBallot, rBallot, rVoted, proposed, learned>>

\* The leader proposes a value for a slot, respecting previously accepted values.
Propose(r, s) ==
    /\ lStatus[r] = "Leading"
    /\ ~ \E m \in msgs : m.type = "Accept" /\ m.bal = lBallot[r] /\ m.slot = s
    /\ \E Q \in Quorums :
        /\ HasPrepareQuorum(Q, lBallot[r])
        /\ LET replies == PrepareRepliesFrom(Q, lBallot[r])
               prevVotes == {m.voted[s] : m \in replies}
               maxBal == CHOOSE mb \in {pv.bal : pv \in prevVotes} :
                             \A pv \in prevVotes : pv.bal <= mb
           IN \E v \in Values :
                /\ IF maxBal = NullBallot
                      THEN TRUE
                      ELSE \E pv \in prevVotes : pv.bal = maxBal /\ pv.val = v
                /\ proposed' = proposed \cup {<<s, v>>}
                /\ Send([type |-> "Accept", src |-> r, bal |-> lBallot[r],
                         slot |-> s, val |-> v])
    /\ UNCHANGED <<lBallot, lStatus, rBallot, rVoted, learned>>

\* An acceptor handles an accept request.
HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ rVoted' = [rVoted EXCEPT ![r][m.slot] = [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "AcceptReply", src |-> r, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

\* A replica learns a value once a majority accepted it in the same ballot.
Learn(r, s) ==
    /\ learned[r][s] = NullValue
    /\ \E b \in Ballots, v \in Values, Q \in Quorums :
        /\ \A q \in Q : \E m \in msgs :
               /\ m.type = "AcceptReply"
               /\ m.src = q
               /\ m.bal = b
               /\ m.slot = s
               /\ m.val = v
        /\ learned' = [learned EXCEPT ![r][s] = v]
    /\ UNCHANGED <<msgs, lBallot, lStatus, rBallot, rVoted, proposed>>

Next ==
    \/ \E r \in Replicas, b \in Ballots : Prepare(r, b)
    \/ \E r \in Replicas : HandlePrepare(r)
    \/ \E r \in Replicas : BecomeLeader(r)
    \/ \E r \in Replicas, s \in Slots : Propose(r, s)
    \/ \E r \in Replicas : HandleAccept(r)
    \/ \E r \in Replicas, s \in Slots : Learn(r, s)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

ConsensusSafety ==
    \A s \in Slots, r1, r2 \in Replicas :
        (learned[r1][s] # NullValue /\ learned[r2][s] # NullValue)
            => learned[r1][s] = learned[r2][s]

Validity ==
    \A r \in Replicas, s \in Slots :
        learned[r][s] # NullValue => <<s, learned[r][s]>> \in proposed

\* Non-triviality check: violating this invariant shows some value can be learned.
NothingLearned ==
    \A r \in Replicas, s \in Slots : learned[r][s] = NullValue

=============================================================================
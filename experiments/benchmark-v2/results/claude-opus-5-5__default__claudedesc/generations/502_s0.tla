---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ IsFiniteSet(Replicas)
       /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Values)
       /\ Cardinality(Values) >= 2
       /\ 0 \notin Values
       /\ Slots # {}
       /\ IsFiniteSet(Slots)
       /\ Ballots # {}
       /\ IsFiniteSet(Ballots)
       /\ Ballots \subseteq Nat

VARIABLES msgs,      \* shared set of messages
          lBallot,   \* leader: current ballot
          lStatus,   \* leader: per-slot phase
          rBallot,   \* acceptor: highest ballot seen
          rVoted,    \* acceptor: last accepted ballot/value per slot
          proposed,  \* global: proposed values per slot
          learned    \* global: learned values per slot

vars == <<msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned>>

NullBallot == -1
NullValue  == 0

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

Statuses == {"", "Preparing", "Accepting", "Learned"}

VoteRec == [bal : Ballots \cup {NullBallot}, val : Values \cup {NullValue}]

PrepareMsgs ==
    [type : {"Prepare"}, from : Replicas, bal : Ballots]

PrepareReplyMsgs ==
    [type : {"PrepareReply"}, from : Replicas, to : Replicas,
     bal : Ballots, voted : [Slots -> VoteRec]]

AcceptMsgs ==
    [type : {"Accept"}, from : Replicas, bal : Ballots,
     slot : Slots, val : Values]

AcceptReplyMsgs ==
    [type : {"AcceptReply"}, from : Replicas, to : Replicas,
     bal : Ballots, slot : Slots, val : Values]

Messages == PrepareMsgs \cup PrepareReplyMsgs \cup AcceptMsgs \cup AcceptReplyMsgs

Send(m) == msgs' = msgs \cup {m}

---------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ lBallot = [r \in Replicas |-> NullBallot]
    /\ lStatus = [r \in Replicas |-> [s \in Slots |-> ""]]
    /\ rBallot = [r \in Replicas |-> NullBallot]
    /\ rVoted  = [r \in Replicas |-> [s \in Slots |-> [bal |-> NullBallot, val |-> NullValue]]]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned  = [s \in Slots |-> {}]

---------------------------------------------------------------------------
\* Phase 1a: leader picks a fresh, higher ballot and broadcasts Prepare.
Prepare(r) ==
    \E b \in Ballots :
        /\ b > lBallot[r]
        /\ ~\E m \in msgs : m.type = "Prepare" /\ m.bal = b
        /\ lBallot' = [lBallot EXCEPT ![r] = b]
        /\ lStatus' = [lStatus EXCEPT ![r] =
                         [s \in Slots |-> IF lStatus[r][s] = "Learned"
                                            THEN "Learned"
                                            ELSE "Preparing"]]
        /\ Send([type |-> "Prepare", from |-> r, bal |-> b])
        /\ UNCHANGED <<rBallot, rVoted, proposed, learned>>

\* Phase 1b: acceptor promises and replies with its full voted record.
PrepareReply(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ Send([type |-> "PrepareReply", from |-> r, to |-> m.from,
                 bal |-> m.bal, voted |-> rVoted[r]])
        /\ UNCHANGED <<lBallot, lStatus, rVoted, proposed, learned>>

\* Select the safe value for slot s given a set of prepare replies R:
\* the value of the highest-ballot vote, or v if no votes were reported.
ValuePreparedIn(R, s, v) ==
    LET votes == {m.voted[s] : m \in R}
        top   == CHOOSE vt \in votes : \A w \in votes : vt.bal >= w.bal
    IN IF votes = {} \/ top.bal = NullBallot THEN v ELSE top.val

\* Phase 2a: leader with a quorum of prepare replies proposes a safe value.
Accept(r, s) ==
    /\ lStatus[r][s] = "Preparing"
    /\ \E Q \in Quorums, v \in Values :
        LET R == {m \in msgs : /\ m.type = "PrepareReply"
                               /\ m.to = r
                               /\ m.bal = lBallot[r]
                               /\ m.from \in Q}
            val == ValuePreparedIn(R, s, v)
        IN /\ \A a \in Q : \E m \in R : m.from = a
           /\ lStatus' = [lStatus EXCEPT ![r][s] = "Accepting"]
           /\ proposed' = [proposed EXCEPT ![s] = @ \cup {val}]
           /\ Send([type |-> "Accept", from |-> r, bal |-> lBallot[r],
                    slot |-> s, val |-> val])
           /\ UNCHANGED <<lBallot, rBallot, rVoted, learned>>

\* Phase 2b: acceptor votes and echoes the vote to the leader.
AcceptReply(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ rVoted' = [rVoted EXCEPT ![r][m.slot] = [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "AcceptReply", from |-> r, to |-> m.from,
                 bal |-> m.bal, slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

\* Learning: leader collects a majority of matching accept replies.
Learn(r, s) ==
    /\ lStatus[r][s] = "Accepting"
    /\ \E Q \in Quorums, v \in Values :
        /\ \A a \in Q : \E m \in msgs :
                /\ m.type = "AcceptReply"
                /\ m.from = a
                /\ m.to = r
                /\ m.bal = lBallot[r]
                /\ m.slot = s
                /\ m.val = v
        /\ lStatus' = [lStatus EXCEPT ![r][s] = "Learned"]
        /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
        /\ UNCHANGED <<msgs, lBallot, rBallot, rVoted, proposed>>

---------------------------------------------------------------------------
Next ==
    \E r \in Replicas :
        \/ Prepare(r)
        \/ PrepareReply(r)
        \/ \E s \in Slots : Accept(r, s)
        \/ AcceptReply(r)
        \/ \E s \in Slots : Learn(r, s)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
\* Auxiliary definitions (not asserted by Spec)
TypeOK ==
    /\ msgs \subseteq Messages
    /\ lBallot \in [Replicas -> Ballots \cup {NullBallot}]
    /\ lStatus \in [Replicas -> [Slots -> Statuses]]
    /\ rBallot \in [Replicas -> Ballots \cup {NullBallot}]
    /\ rVoted \in [Replicas -> [Slots -> VoteRec]]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Slots -> SUBSET Values]

Nontriviality == \A s \in Slots : learned[s] \subseteq proposed[s]

Consistency == \A s \in Slots : Cardinality(learned[s]) <= 1

=============================================================================
------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Proposers, Acceptors, Quorums, Learners, Values, Slots, Ballots

ASSUME Cardinality(Acceptors) >= 3
ASSUME Quorums \subseteq SUBSET Acceptors
ASSUME \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME Cardinality(Values) >= 2
ASSUME Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

NoBallot == -1

VoteRec == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]

NoVote == [bal |-> NoBallot, val |-> None]

VARIABLES msgs, pBallot, aBallot, aVoted, proposed, learned

vars == <<msgs, pBallot, aBallot, aVoted, proposed, learned>>

Phase1aMsg == [type : {"1a"}, from : Proposers, bal : Ballots]
Phase1bMsg == [type : {"1b"}, acc : Acceptors, bal : Ballots, voted : [Slots -> VoteRec]]
Phase2aMsg == [type : {"2a"}, from : Proposers, bal : Ballots, slot : Slots, val : Values]
Phase2bMsg == [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

Messages == Phase1aMsg \cup Phase1bMsg \cup Phase2aMsg \cup Phase2bMsg

TypeOK ==
    /\ msgs \subseteq Messages
    /\ pBallot \in [Proposers -> Ballots \cup {NoBallot}]
    /\ aBallot \in [Acceptors -> Ballots \cup {NoBallot}]
    /\ aVoted \in [Acceptors -> [Slots -> VoteRec]]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Learners -> [Slots -> SUBSET Values]]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ pBallot = [p \in Proposers |-> NoBallot]
    /\ aBallot = [a \in Acceptors |-> NoBallot]
    /\ aVoted = [a \in Acceptors |-> [s \in Slots |-> NoVote]]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [l \in Learners |-> [s \in Slots |-> {}]]

-----------------------------------------------------------------------------
(* Proposer actions *)

\* Phase 1a: broadcast a prepare for a fresh (never used) ballot
Phase1a(p, b) ==
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ pBallot' = [pBallot EXCEPT ![p] = b]
    /\ Send([type |-> "1a", from |-> p, bal |-> b])
    /\ UNCHANGED <<aBallot, aVoted, proposed, learned>>

\* Value selection rule over the Phase 1b messages of a quorum
SafeValue(S, s, v) ==
    \/ \A m \in S : m.voted[s].bal = NoBallot
    \/ \E m \in S :
          /\ m.voted[s].bal # NoBallot
          /\ m.voted[s].val = v
          /\ \A m2 \in S : m2.voted[s].bal <= m.voted[s].bal

\* Phase 2a: send an accept for a slot and value
Phase2a(p, s, v) ==
    LET b == pBallot[p] IN
    /\ b # NoBallot
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET S == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
         IN /\ \A a \in Q : \E m \in S : m.acc = a
            /\ SafeValue(S, s, v)
    /\ Send([type |-> "2a", from |-> p, bal |-> b, slot |-> s, val |-> v])
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<pBallot, aBallot, aVoted, learned>>

Proposer(p) ==
    \/ \E b \in Ballots : Phase1a(p, b)
    \/ \E s \in Slots, v \in Values : Phase2a(p, s, v)

-----------------------------------------------------------------------------
(* Acceptor actions *)

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > aBallot[a]
        /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, voted |-> aVoted[a]])
        /\ UNCHANGED <<pBallot, aVoted, proposed, learned>>

Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= aBallot[a]
        /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
        /\ aVoted' = [aVoted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<pBallot, proposed, learned>>

Acceptor(a) == Phase1b(a) \/ Phase2b(a)

-----------------------------------------------------------------------------
(* Learner actions *)

Learn(l, s) ==
    /\ learned[l][s] = {}
    /\ \E b \in Ballots, v \in Values, Q \in Quorums :
         /\ \A a \in Q : \E m \in msgs :
               /\ m.type = "2b"
               /\ m.acc = a
               /\ m.bal = b
               /\ m.slot = s
               /\ m.val = v
         /\ learned' = [learned EXCEPT ![l][s] = {v}]
    /\ UNCHANGED <<msgs, pBallot, aBallot, aVoted, proposed>>

Learner(l) == \E s \in Slots : Learn(l, s)

-----------------------------------------------------------------------------
Next ==
    \/ \E p \in Proposers : Proposer(p)
    \/ \E a \in Acceptors : Acceptor(a)
    \/ \E l \in Learners : Learner(l)

Spec == Init /\ [][Next]_vars

=============================================================================
---- MODULE MultiPaxosAggregatedPrepare ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ IsFiniteSet(Replicas) /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Values)   /\ Cardinality(Values) >= 2
       /\ IsFiniteSet(Slots)    /\ Slots # {}  /\ Slots \subseteq Nat
       /\ IsFiniteSet(Ballots)  /\ Ballots # {} /\ Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

N == Cardinality(Replicas)

RepIndex == CHOOSE f \in [Replicas -> 1..N] :
                \A a, b \in Replicas : f[a] = f[b] => a = b

\* Each replica owns a disjoint set of ballot numbers (all > 0)
BNum(b, r) == b * N + RepIndex[r]

OwnBallots(r) == { BNum(b, r) : b \in Ballots }

BallotNums == { BNum(b, r) : b \in Ballots, r \in Replicas }

Quorums == { Q \in SUBSET Replicas : 2 * Cardinality(Q) > N }

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Vote == [bal : BallotNums \cup {-1}, val : Values \cup {None}]

VARIABLES msgs,      \* set of all messages sent
          ballot,    \* ballot[r]: highest ballot number seen / promised by r
          aBal,      \* aBal[r][s]: ballot in which r last accepted in slot s
          aVal,      \* aVal[r][s]: value r last accepted in slot s
          learned    \* learned[r][s]: value learned by r for slot s

vars == << msgs, ballot, aBal, aVal, learned >>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ ballot  \in [Replicas -> BallotNums \cup {0}]
    /\ aBal    \in [Replicas -> [Slots -> BallotNums \cup {-1}]]
    /\ aVal    \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ learned \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ \A m \in msgs : m.type \in {"prepare", "prepareReply", "accept",
                                   "acceptReply", "learn"}

Init ==
    /\ msgs    = {}
    /\ ballot  = [r \in Replicas |-> 0]
    /\ aBal    = [r \in Replicas |-> [s \in Slots |-> -1]]
    /\ aVal    = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ learned = [r \in Replicas |-> [s \in Slots |-> None]]

\* Phase 1a: a single (aggregated) Prepare covers all slots
SendPrepare(r, b) ==
    /\ BNum(b, r) > ballot[r]
    /\ ballot' = [ballot EXCEPT ![r] = BNum(b, r)]
    /\ Send([type |-> "prepare", from |-> r, bal |-> BNum(b, r)])
    /\ UNCHANGED << aBal, aVal, learned >>

\* Phase 1b: reply with votes for all slots
HandlePrepare(r, m) ==
    /\ m.type = "prepare"
    /\ m.bal >= ballot[r]
    /\ ballot' = [ballot EXCEPT ![r] = m.bal]
    /\ Send([type  |-> "prepareReply", from |-> r, to |-> m.from,
             bal   |-> m.bal,
             voted |-> [s \in Slots |-> [bal |-> aBal[r][s], val |-> aVal[r][s]]]])
    /\ UNCHANGED << aBal, aVal, learned >>

\* Phase 2a: after a quorum of PrepareReplies, propose a safe value for slot s
SendAccept(r, s) ==
    /\ ballot[r] \in OwnBallots(r)
    /\ ~ \E m \in msgs : /\ m.type = "accept" /\ m.from = r
                         /\ m.bal = ballot[r] /\ m.slot = s
    /\ \E Q \in Quorums :
         LET replies == { m \in msgs : /\ m.type = "prepareReply"
                                       /\ m.to = r
                                       /\ m.bal = ballot[r]
                                       /\ m.from \in Q }
             votes   == { m.voted[s] : m \in replies }
         IN /\ \A q \in Q : \E m \in replies : m.from = q
            /\ LET maxb == Max({ vt.bal : vt \in votes })
               IN \E v \in Values :
                    /\ \/ maxb = -1
                       \/ \E vt \in votes : vt.bal = maxb /\ vt.val = v
                    /\ Send([type |-> "accept", from |-> r, bal |-> ballot[r],
                             slot |-> s, val |-> v])
    /\ UNCHANGED << ballot, aBal, aVal, learned >>

\* Phase 2b
HandleAccept(r, m) ==
    /\ m.type = "accept"
    /\ m.bal >= ballot[r]
    /\ ballot' = [ballot EXCEPT ![r] = m.bal]
    /\ aBal' = [aBal EXCEPT ![r][m.slot] = m.bal]
    /\ aVal' = [aVal EXCEPT ![r][m.slot] = m.val]
    /\ Send([type |-> "acceptReply", from |-> r, to |-> m.from,
             bal |-> m.bal, slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED learned

\* Proposer learns on a quorum of AcceptReplies and broadcasts Learn
HandleAcceptReply(r, s) ==
    /\ \E Q \in Quorums, b \in BallotNums, v \in Values :
         /\ \A q \in Q : \E m \in msgs : /\ m.type = "acceptReply"
                                        /\ m.to = r /\ m.from = q
                                        /\ m.bal = b /\ m.slot = s
                                        /\ m.val = v
         /\ learned' = [learned EXCEPT ![r][s] = v]
         /\ Send([type |-> "learn", from |-> r, slot |-> s, val |-> v])
    /\ UNCHANGED << ballot, aBal, aVal >>

HandleLearn(r, m) ==
    /\ m.type = "learn"
    /\ learned' = [learned EXCEPT ![r][m.slot] = m.val]
    /\ UNCHANGED << msgs, ballot, aBal, aVal >>

Next ==
    \E r \in Replicas :
        \/ \E b \in Ballots : SendPrepare(r, b)
        \/ \E m \in msgs : HandlePrepare(r, m)
        \/ \E s \in Slots : SendAccept(r, s)
        \/ \E m \in msgs : HandleAccept(r, m)
        \/ \E s \in Slots : HandleAcceptReply(r, s)
        \/ \E m \in msgs : HandleLearn(r, m)

Spec == Init /\ [][Next]_vars

\* Safety: at most one value is learned per slot across all replicas
Consistency ==
    \A r1, r2 \in Replicas, s \in Slots :
        (learned[r1][s] # None /\ learned[r2][s] # None)
            => learned[r1][s] = learned[r2][s]

\* Only proposed values can be learned
Validity ==
    \A r \in Replicas, s \in Slots :
        learned[r][s] # None =>
            \E m \in msgs : m.type = "accept" /\ m.slot = s /\ m.val = learned[r][s]

THEOREM Spec => [](TypeOK /\ Consistency /\ Validity)
====
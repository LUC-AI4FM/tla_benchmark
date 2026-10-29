------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,          \* number of replicas; replicas are identified by 1..N
    Slots,      \* finite set of log slots (sequence positions)
    Values,     \* finite set of values that may be proposed
    MaxBallot   \* largest ballot number; ballots are 0..MaxBallot

ASSUME /\ N \in Nat \ {0}
       /\ MaxBallot \in Nat
       /\ Slots # {}
       /\ Values # {}

Replicas == 1..N
Ballots  == 0..MaxBallot
NoBallot == -1
None     == CHOOSE v : v \notin Values

\* Each ballot is owned by exactly one replica, so distinct proposers
\* never use the same ballot.
Owner(b) == (b % N) + 1

\* Majority quorums: any two quorums intersect.
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > N}

\* The replica owning the highest ballot. It is used only in the
\* liveness assumption.
Leader == Owner(MaxBallot)

-----------------------------------------------------------------------------
\* Message domains

PrepareMsg ==
    [type : {"prepare"}, from : Replicas, slot : Slots, bal : Ballots]

PrepareReplyMsg ==
    [type : {"preparereply"}, from : Replicas, to : Replicas, slot : Slots,
     bal : Ballots, vbal : Ballots \cup {NoBallot}, vval : Values \cup {None}]

AcceptMsg ==
    [type : {"accept"}, from : Replicas, slot : Slots, bal : Ballots,
     val : Values]

AcceptReplyMsg ==
    [type : {"acceptreply"}, from : Replicas, to : Replicas, slot : Slots,
     bal : Ballots, val : Values]

Messages == PrepareMsg \cup PrepareReplyMsg \cup AcceptMsg \cup AcceptReplyMsg

Vote == [slot : Slots, bal : Ballots, val : Values]

-----------------------------------------------------------------------------
VARIABLES
    proposals,  \* proposals[r][s]: the values replica r proposes for slot s
    maxBal,     \* maxBal[r][s]: the highest ballot replica r has promised for slot s
    maxVBal,    \* maxVBal[r][s]: the highest ballot in which r voted for slot s
    maxVal,     \* maxVal[r][s]: the value r voted for in ballot maxVBal[r][s]
    votes,      \* votes[r]: persistent history of every vote cast by r
    msgs,       \* the set of messages ever sent; delivery is nondeterministic
    learned     \* learned[s]: the set of values learned for slot s

vars == <<proposals, maxBal, maxVBal, maxVal, votes, msgs, learned>>

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
    /\ proposals = [r \in Replicas |-> [s \in Slots |-> {}]]
    /\ maxBal    = [r \in Replicas |-> [s \in Slots |-> NoBallot]]
    /\ maxVBal   = [r \in Replicas |-> [s \in Slots |-> NoBallot]]
    /\ maxVal    = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ votes     = [r \in Replicas |-> {}]
    /\ msgs      = {}
    /\ learned   = [s \in Slots |-> {}]

\* A replica adds a value to its proposal set for a slot.
Propose(r, s, v) ==
    /\ v \notin proposals[r][s]
    /\ proposals' = [proposals EXCEPT ![r][s] = @ \cup {v}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, msgs, learned>>

\* Phase 1a: the owner of ballot b sends Prepare for slot s.
Phase1a(r, s, b) ==
    /\ Owner(b) = r
    /\ Send([type |-> "prepare", from |-> r, slot |-> s, bal |-> b])
    /\ UNCHANGED <<proposals, maxBal, maxVBal, maxVal, votes, learned>>

\* Phase 1b: an acceptor promises ballot m.bal and reports its last vote.
Phase1b(a, m) ==
    /\ m \in msgs
    /\ m.type = "prepare"
    /\ m.bal > maxBal[a][m.slot]
    /\ maxBal' = [maxBal EXCEPT ![a][m.slot] = m.bal]
    /\ Send([type |-> "preparereply", from |-> a, to |-> m.from,
             slot |-> m.slot, bal |-> m.bal,
             vbal |-> maxVBal[a][m.slot], vval |-> maxVal[a][m.slot]])
    /\ UNCHANGED <<proposals, maxVBal, maxVal, votes, learned>>

\* Phase 2a: after a quorum of PrepareReplies, the owner of ballot b sends
\* Accept. The value is the one voted in the highest reported ballot. If no
\* replica in the quorum has voted, the value is any value from the
\* proposer's own proposal set. A proposer sends at most one Accept per
\* (slot, ballot).
Phase2a(r, s, b, v) ==
    /\ Owner(b) = r
    /\ ~ \E m \in msgs : m.type = "accept" /\ m.slot = s /\ m.bal = b
    /\ \E Q \in Quorums :
         LET R == {m \in msgs : /\ m.type = "preparereply"
                                /\ m.to = r /\ m.slot = s
                                /\ m.bal = b /\ m.from \in Q}
         IN /\ \A q \in Q : \E m \in R : m.from = q
            /\ \/ /\ \A m \in R : m.vbal = NoBallot
                  /\ v \in proposals[r][s]
               \/ \E m \in R : /\ m.vbal # NoBallot
                               /\ m.vval = v
                               /\ \A m2 \in R : m2.vbal <= m.vbal
    /\ Send([type |-> "accept", from |-> r, slot |-> s, bal |-> b, val |-> v])
    /\ UNCHANGED <<proposals, maxBal, maxVBal, maxVal, votes, learned>>

\* Phase 2b: an acceptor votes for an Accept unless it has promised a higher
\* ballot.
Phase2b(a, m) ==
    /\ m \in msgs
    /\ m.type = "accept"
    /\ m.bal >= maxBal[a][m.slot]
    /\ maxBal'  = [maxBal  EXCEPT ![a][m.slot] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a][m.slot] = m.val]
    /\ votes'   = [votes   EXCEPT ![a] =
                      @ \cup {[slot |-> m.slot, bal |-> m.bal, val |-> m.val]}]
    /\ Send([type |-> "acceptreply", from |-> a, to |-> m.from,
             slot |-> m.slot, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED <<proposals, learned>>

\* A learner learns v for slot s when a quorum has sent AcceptReply for
\* (s, b, v).
Learn(s, b, v) ==
    /\ \E Q \in Quorums :
         \A q \in Q :
           [type |-> "acceptreply", from |-> q, to |-> Owner(b),
            slot |-> s, bal |-> b, val |-> v] \in msgs
    /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<proposals, maxBal, maxVBal, maxVal, votes, msgs>>

Next ==
    \/ \E r \in Replicas, s \in Slots, v \in Values : Propose(r, s, v)
    \/ \E r \in Replicas, s \in Slots, b \in Ballots : Phase1a(r, s, b)
    \/ \E a \in Replicas, m \in msgs : Phase1b(a, m)
    \/ \E r \in Replicas, s \in Slots, b \in Ballots, v \in Values :
          Phase2a(r, s, b, v)
    \/ \E a \in Replicas, m \in msgs : Phase2b(a, m)
    \/ \E s \in Slots, b \in Ballots, v \in Values : Learn(s, b, v)

\* Safety specification. Messages may be lost (never received), delayed,
\* or duplicated. Scheduling is fully nondeterministic.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Liveness: the stable leader runs the highest ballot MaxBallot, which no
\* other replica can preempt. All replicas respond, and the leader's
\* messages are eventually delivered.

LeaderPhase1a(s) == Phase1a(Leader, s, MaxBallot)

LeaderPhase1b(a, s) ==
    \E m \in msgs : /\ m.type = "prepare" /\ m.slot = s
                    /\ m.bal = MaxBallot /\ Phase1b(a, m)

LeaderPhase2a(s) == \E v \in Values : Phase2a(Leader, s, MaxBallot, v)

LeaderPhase2b(a, s) ==
    \E m \in msgs : /\ m.type = "accept" /\ m.slot = s
                    /\ m.bal = MaxBallot /\ Phase2b(a, m)

LeaderLearn(s) == \E v \in Values : Learn(s, MaxBallot, v)

Fairness ==
    \A s \in Slots :
        /\ WF_vars(LeaderPhase1a(s))
        /\ \A a \in Replicas : WF_vars(LeaderPhase1b(a, s))
        /\ WF_vars(LeaderPhase2a(s))
        /\ \A a \in Replicas : WF_vars(LeaderPhase2b(a, s))
        /\ WF_vars(LeaderLearn(s))

LiveSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
\* Typing invariant

TypeOK ==
    /\ proposals \in [Replicas -> [Slots -> SUBSET Values]]
    /\ maxBal    \in [Replicas -> [Slots -> Ballots \cup {NoBallot}]]
    /\ maxVBal   \in [Replicas -> [Slots -> Ballots \cup {NoBallot}]]
    /\ maxVal    \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ votes     \in [Replicas -> SUBSET Vote]
    /\ msgs      \subseteq Messages
    /\ learned   \in [Slots -> SUBSET Values]

\* Local state is well formed: the promise is at least the last vote, and
\* the last vote is recorded in the persistent vote history.
LocalStateOK ==
    \A a \in Replicas, s \in Slots :
        /\ maxVBal[a][s] <= maxBal[a][s]
        /\ (maxVBal[a][s] = NoBallot) <=> (maxVal[a][s] = None)
        /\ maxVBal[a][s] # NoBallot =>
              [slot |-> s, bal |-> maxVBal[a][s], val |-> maxVal[a][s]] \in votes[a]
        /\ \A vt \in votes[a] : vt.slot = s => vt.bal <= maxVBal[a][s]

\* Safety invariants

\* Nontriviality: a learned value was proposed for that slot.
Nontriviality ==
    \A s \in Slots :
        learned[s] \subseteq UNION {proposals[r][s] : r \in Replicas}

\* Consistency (agreement): at most one value is learned per slot.
Consistency ==
    \A s \in Slots : \A v1, v2 \in learned[s] : v1 = v2

\* Validity of replies: a PrepareReply faithfully reports the responder's
\* highest vote below the prepared ballot, or reports no vote if none exists.
PrepareReplyValidity ==
    \A m \in msgs :
        m.type = "preparereply" =>
            LET a == m.from
                s == m.slot
            IN /\ maxBal[a][s] >= m.bal
               /\ m.vbal = NoBallot =>
                     /\ m.vval = None
                     /\ \A vt \in votes[a] : vt.slot = s => vt.bal >= m.bal
               /\ m.vbal # NoBallot =>
                     /\ m.vbal < m.bal
                     /\ [slot |-> s, bal |-> m.vbal, val |-> m.vval] \in votes[a]
                     /\ \A vt \in votes[a] :
                           (vt.slot = s /\ vt.bal < m.bal) => vt.bal <= m.vbal

\* An AcceptReply reflects a real vote. That vote matches the unique Accept
\* for its slot and ballot.
AcceptReplyValidity ==
    \A m \in msgs :
        m.type = "acceptreply" =>
            /\ [slot |-> m.slot, bal |-> m.bal, val |-> m.val] \in votes[m.from]
            /\ [type |-> "accept", from |-> m.to, slot |-> m.slot,
                bal |-> m.bal, val |-> m.val] \in msgs

\* At most one Accept is sent per (slot, ballot).
UniqueAccept ==
    \A m1, m2 \in msgs :
        (m1.type = "accept" /\ m2.type = "accept" /\
         m1.slot = m2.slot /\ m1.bal = m2.bal) => m1 = m2

Inv ==
    /\ TypeOK
    /\ LocalStateOK
    /\ Nontriviality
    /\ Consistency
    /\ PrepareReplyValidity
    /\ AcceptReplyValidity
    /\ UniqueAccept

\* Stability: learned sets only grow.
Stability ==
    [][\A s \in Slots : learned[s] \subseteq learned'[s]]_vars

\* Liveness, under LiveSpec: if the leader proposes a value for a slot,
\* some value is eventually learned for that slot.
Liveness ==
    \A s \in Slots : (proposals[Leader][s] # {}) ~> (learned[s] # {})

THEOREM Spec => []Inv
THEOREM Spec => Stability
THEOREM LiveSpec => Liveness
=============================================================================
---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proposers,   \* set of proposer ids
          Acceptors,   \* set of acceptor ids
          Learners,    \* set of learner ids
          Values,      \* set of proposable values
          Slots,       \* set of log positions (instances)
          MaxBallot    \* largest ballot number

ASSUME MaxBallot \in Nat
ASSUME Acceptors # {} /\ IsFiniteSet(Acceptors)

Ballots == 0..MaxBallot
NoBallot == -1
None == CHOOSE v : v \notin Values

\* Majority quorums: any two intersect
Quorums == {Q \in SUBSET Acceptors : 2 * Cardinality(Q) > Cardinality(Acceptors)}

VoteRec == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]
NoVote  == [bal |-> NoBallot, val |-> None]

Messages ==
       [type : {"1a"}, prop : Proposers, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots, accs : [Slots -> VoteRec]]
  \cup [type : {"2a"}, prop : Proposers, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

VARIABLES msgs,       \* set of all messages sent
          maxBal,     \* maxBal[a]: highest ballot acceptor a has participated in
          accepted,   \* accepted[a][s]: last vote cast by a in slot s
          proposed,   \* proposed[s]: values proposed for slot s
          learned     \* learned[l][s]: values learned by learner l in slot s

vars == <<msgs, maxBal, accepted, proposed, learned>>

TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxBal \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ accepted \in [Acceptors -> [Slots -> VoteRec]]
  /\ proposed \in [Slots -> SUBSET Values]
  /\ learned \in [Learners -> [Slots -> SUBSET Values]]

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ msgs = {}
  /\ maxBal = [a \in Acceptors |-> NoBallot]
  /\ accepted = [a \in Acceptors |-> [s \in Slots |-> NoVote]]
  /\ proposed = [s \in Slots |-> {}]
  /\ learned = [l \in Learners |-> [s \in Slots |-> {}]]

\* A client/proposer proposes value v for slot s
Propose(p, s, v) ==
  /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
  /\ UNCHANGED <<msgs, maxBal, accepted, learned>>

\* Phase 1a: proposer p starts ballot b (covers all slots)
Phase1a(p, b) ==
  /\ Send([type |-> "1a", prop |-> p, bal |-> b])
  /\ UNCHANGED <<maxBal, accepted, proposed, learned>>

\* Phase 1b: acceptor promises and reports its votes for every slot
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, accs |-> accepted[a]])
    /\ UNCHANGED <<accepted, proposed, learned>>

\* Phase 2a: proposer p, having a quorum of promises for b, proposes v in slot s
Phase2a(p, b, s, v) ==
  /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       \E S \in SUBSET {m \in msgs : m.type = "1b" /\ m.bal = b} :
         /\ \A a \in Q : \E m \in S : m.acc = a
         /\ \A m \in S : m.acc \in Q
         /\ LET votes    == {m.accs[s] : m \in S}
                withVals == {r \in votes : r.bal # NoBallot}
            IN \/ /\ withVals = {}
                  /\ v \in proposed[s]
               \/ \E r \in withVals :
                    /\ r.val = v
                    /\ \A r2 \in withVals : r2.bal <= r.bal
  /\ Send([type |-> "2a", prop |-> p, bal |-> b, slot |-> s, val |-> v])
  /\ UNCHANGED <<maxBal, accepted, proposed, learned>>

\* Phase 2b: acceptor accepts a proposal not below its promise
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ accepted' = [accepted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED <<proposed, learned>>

\* Learner learns v in slot s once a quorum accepted it in the same ballot
Learn(l, s) ==
  \E b \in Ballots, v \in Values, Q \in Quorums :
    /\ \A a \in Q : \E m \in msgs :
         /\ m.type = "2b" /\ m.acc = a /\ m.bal = b
         /\ m.slot = s /\ m.val = v
    /\ learned' = [learned EXCEPT ![l][s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, maxBal, accepted, proposed>>

Next ==
  \/ \E p \in Proposers, s \in Slots, v \in Values : Propose(p, s, v)
  \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
  \/ \E a \in Acceptors : Phase1b(a)
  \/ \E p \in Proposers, b \in Ballots, s \in Slots, v \in Values : Phase2a(p, b, s, v)
  \/ \E a \in Acceptors : Phase2b(a)
  \/ \E l \in Learners, s \in Slots : Learn(l, s)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

NonTriviality ==
  \A l \in Learners, s \in Slots : learned[l][s] \subseteq proposed[s]

Consistency ==
  \A l1, l2 \in Learners, s \in Slots :
    \A v1 \in learned[l1][s], v2 \in learned[l2][s] : v1 = v2

Stability ==
  \A l \in Learners, s \in Slots, v \in Values :
    [](v \in learned[l][s] => [](v \in learned[l][s]))

StabilityAction ==
  [][\A l \in Learners, s \in Slots : learned[l][s] \subseteq learned'[l][s]]_vars

Inv == TypeOK /\ NonTriviality /\ Consistency

-----------------------------------------------------------------------------
\* Abstract multi-slot consensus specification (refinement target)

chosenAbs   == [s \in Slots |-> UNION {learned[l][s] : l \in Learners}]
proposedAbs == proposed

AbsInit ==
  /\ chosenAbs = [s \in Slots |-> {}]
  /\ proposedAbs = [s \in Slots |-> {}]

AbsPropose(s, v) ==
  /\ proposedAbs' = [proposedAbs EXCEPT ![s] = @ \cup {v}]
  /\ chosenAbs' = chosenAbs

AbsChoose(s, v) ==
  /\ v \in proposedAbs[s]
  /\ chosenAbs[s] = {}
  /\ chosenAbs' = [chosenAbs EXCEPT ![s] = {v}]
  /\ proposedAbs' = proposedAbs

AbsNext == \E s \in Slots, v \in Values : AbsPropose(s, v) \/ AbsChoose(s, v)

AbsSpec == AbsInit /\ [][AbsNext]_<<chosenAbs, proposedAbs>>

THEOREM Spec => []Inv
THEOREM Spec => Stability
THEOREM Spec => StabilityAction
THEOREM Spec => AbsSpec
=============================================================================
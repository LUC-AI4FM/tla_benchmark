------------------------------ MODULE MultiPaxos ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors,   \* set of acceptors
          Ballots,     \* set of ballot numbers (natural numbers)
          Learners,    \* set of learners
          Proposers,   \* set of proposers
          Quorums,     \* set of quorums (subsets of Acceptors)
          Slots,       \* set of slots / instances / decrees
          Values       \* set of proposable values

ASSUME QuorumAssumption ==
          /\ \A Q \in Quorums : Q \subseteq Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

VARIABLES aBallot,   \* aBallot[a]: highest ballot acceptor a has promised/participated in
          aVoted,    \* aVoted[a]: set of votes [bal, slot, val] of acceptor a (latest per slot)
          pBallot,   \* pBallot[p]: current ballot of proposer p (-1 if none)
          proposed,  \* set of proposals [bal, slot, val] issued by proposers
          learned,   \* learned[l][s]: set of values learner l has learned for slot s
          msgs       \* the pool of all messages ever sent

vars == <<aBallot, aVoted, pBallot, proposed, learned, msgs>>

NoBallot == -1

Vote == [bal : Ballots, slot : Slots, val : Values]

Messages ==
       [type : {"1a"}, bal : Ballots, prop : Proposers]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots, votes : SUBSET Vote]
  \cup [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

TypeOK ==
  /\ aBallot \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ aVoted \in [Acceptors -> SUBSET Vote]
  /\ pBallot \in [Proposers -> Ballots \cup {NoBallot}]
  /\ proposed \subseteq Vote
  /\ learned \in [Learners -> [Slots -> SUBSET Values]]
  /\ msgs \subseteq Messages

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ aBallot = [a \in Acceptors |-> NoBallot]
  /\ aVoted = [a \in Acceptors |-> {}]
  /\ pBallot = [p \in Proposers |-> NoBallot]
  /\ proposed = {}
  /\ learned = [l \in Learners |-> [s \in Slots |-> {}]]
  /\ msgs = {}

-----------------------------------------------------------------------------
(* Phase 1a: proposer p starts a new (globally unique) ballot b.            *)
(* The prepare phase is aggregated over all slots.                          *)
Phase1a(p, b) ==
  /\ b > pBallot[p]
  /\ ~\E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ pBallot' = [pBallot EXCEPT ![p] = b]
  /\ Send([type |-> "1a", bal |-> b, prop |-> p])
  /\ UNCHANGED <<aBallot, aVoted, proposed, learned>>

(* Phase 1b: acceptor a promises ballot b, reporting its votes for all slots *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > aBallot[a]
    /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, votes |-> aVoted[a]])
    /\ UNCHANGED <<aVoted, pBallot, proposed, learned>>

(* Proposer p, having completed phase 1 for ballot b with quorum Q,         *)
(* proposes value v for slot s.                                             *)
Phase2a(p, s, v) ==
  LET b == pBallot[p] IN
  /\ b # NoBallot
  /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       LET Q1b   == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
           votes == {vt \in UNION {m.votes : m \in Q1b} : vt.slot = s}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ votes = {}
              \/ \E vt \in votes :
                   /\ vt.val = v
                   /\ \A w \in votes : w.bal <= vt.bal
  /\ proposed' = proposed \cup {[bal |-> b, slot |-> s, val |-> v]}
  /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
  /\ UNCHANGED <<aBallot, aVoted, pBallot, learned>>

(* Phase 2b: acceptor a votes for a 2a proposal                              *)
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= aBallot[a]
    /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
    /\ aVoted' = [aVoted EXCEPT ![a] =
                    {vt \in aVoted[a] : vt.slot # m.slot}
                      \cup {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]}]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal,
             slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED <<pBallot, proposed, learned>>

(* Learner l learns v for slot s once a quorum voted for it in one ballot   *)
Learn(l, s, v) ==
  /\ v \notin learned[l][s]
  /\ \E b \in Ballots, Q \in Quorums :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "2b" /\ m.acc = a /\ m.bal = b
          /\ m.slot = s /\ m.val = v
  /\ learned' = [learned EXCEPT ![l][s] = @ \cup {v}]
  /\ UNCHANGED <<aBallot, aVoted, pBallot, proposed, msgs>>

Next ==
  \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
  \/ \E a \in Acceptors : Phase1b(a)
  \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
  \/ \E a \in Acceptors : Phase2b(a)
  \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

VotedFor(a, b, s, v) ==
  \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.slot = s /\ m.val = v

ChosenAt(b, s, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, s, v)

Chosen(s, v) == \E b \in Ballots : ChosenAt(b, s, v)

Agreement ==
  \A s \in Slots : \A v1, v2 \in Values :
     (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2

LearnerAgreement ==
  \A l1, l2 \in Learners : \A s \in Slots :
     \A v1 \in learned[l1][s], v2 \in learned[l2][s] : v1 = v2

Validity ==
  /\ \A s \in Slots, v \in Values :
       Chosen(s, v) => \E pr \in proposed : pr.slot = s /\ pr.val = v
  /\ \A l \in Learners, s \in Slots :
       \A v \in learned[l][s] : \E pr \in proposed : pr.slot = s /\ pr.val = v

Safety == TypeOK /\ Agreement /\ LearnerAgreement /\ Validity

THEOREM Spec => []Safety
=============================================================================
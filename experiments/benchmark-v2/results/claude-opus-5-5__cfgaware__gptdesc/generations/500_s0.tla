---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Proposers, Learners, Values, Ballots, Slots, Quorums

ASSUME /\ Ballots \subseteq Nat
       /\ \A Q \in Quorums : Q \subseteq Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

NoBallot == -1

VARIABLES msgs,      \* monotonic set of all sent messages
          pBallot,   \* current ballot of each proposer
          aBallot,   \* highest ballot promised by each acceptor
          aVoted,    \* per acceptor, per slot: last vote [bal, val]
          proposed,  \* set of proposals [slot, bal, val] issued by proposers
          learned    \* per learner, per slot: learned (committed) value

vars == <<msgs, pBallot, aBallot, aVoted, proposed, learned>>

VoteRec == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]

TypeOK ==
  /\ pBallot \in [Proposers -> Ballots \cup {NoBallot}]
  /\ aBallot \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ aVoted \in [Acceptors -> [Slots -> VoteRec]]
  /\ proposed \subseteq [slot : Slots, bal : Ballots, val : Values]
  /\ learned \in [Learners -> [Slots -> Values \cup {None}]]

Init ==
  /\ msgs = {}
  /\ pBallot = [p \in Proposers |-> NoBallot]
  /\ aBallot = [a \in Acceptors |-> NoBallot]
  /\ aVoted = [a \in Acceptors |-> [s \in Slots |-> [bal |-> NoBallot, val |-> None]]]
  /\ proposed = {}
  /\ learned = [l \in Learners |-> [s \in Slots |-> None]]

Send(m) == msgs' = msgs \cup {m}

(* Phase 1a: a proposer picks a fresh, unused, higher ballot and sends prepare *)
Phase1a(p, b) ==
  /\ b > pBallot[p]
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ pBallot' = [pBallot EXCEPT ![p] = b]
  /\ Send([type |-> "1a", bal |-> b, prop |-> p])
  /\ UNCHANGED <<aBallot, aVoted, proposed, learned>>

(* Phase 1b: an acceptor promises and reports its votes for all slots *)
Phase1b(a, m) ==
  /\ m.type = "1a"
  /\ m.bal > aBallot[a]
  /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
  /\ Send([type |-> "1b", bal |-> m.bal, acc |-> a, voted |-> aVoted[a]])
  /\ UNCHANGED <<pBallot, aVoted, proposed, learned>>

(* Phase 2a: having a quorum of promises, the proposer proposes a safe value *)
Phase2a(p, s, v) ==
  LET b == pBallot[p] IN
  /\ b # NoBallot
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
           Q1bv == {m \in Q1b : m.voted[s].bal # NoBallot}
       IN /\ \A a \in Q : \E m \in Q1b : m.acc = a
          /\ \/ Q1bv = {}
             \/ \E m \in Q1bv :
                  /\ m.voted[s].val = v
                  /\ \A mm \in Q1bv : mm.voted[s].bal <= m.voted[s].bal
  /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
  /\ proposed' = proposed \cup {[slot |-> s, bal |-> b, val |-> v]}
  /\ UNCHANGED <<pBallot, aBallot, aVoted, learned>>

(* Phase 2b: an acceptor accepts a proposal *)
Phase2b(a, m) ==
  /\ m.type = "2a"
  /\ m.bal >= aBallot[a]
  /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
  /\ aVoted' = [aVoted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
  /\ Send([type |-> "2b", bal |-> m.bal, slot |-> m.slot, val |-> m.val, acc |-> a])
  /\ UNCHANGED <<pBallot, proposed, learned>>

(* Commit notice: once a quorum accepted, a commit notice is broadcast *)
Commit(s, b, v) ==
  /\ ~ \E m \in msgs : m.type = "commit" /\ m.slot = s /\ m.val = v
  /\ \E Q \in Quorums :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "2b" /\ m.acc = a
          /\ m.slot = s /\ m.bal = b /\ m.val = v
  /\ Send([type |-> "commit", slot |-> s, val |-> v])
  /\ UNCHANGED <<pBallot, aBallot, aVoted, proposed, learned>>

(* Learner learns a committed value *)
Learn(l, m) ==
  /\ m.type = "commit"
  /\ learned[l][m.slot] = None
  /\ learned' = [learned EXCEPT ![l][m.slot] = m.val]
  /\ UNCHANGED <<msgs, pBallot, aBallot, aVoted, proposed>>

AllDone == \A l \in Learners : \A s \in Slots : learned[l][s] # None

(* Explicit stuttering after termination to avoid deadlock *)
Terminating ==
  /\ AllDone
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
  \/ \E a \in Acceptors, m \in msgs : Phase1b(a, m)
  \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
  \/ \E a \in Acceptors, m \in msgs : Phase2b(a, m)
  \/ \E s \in Slots, b \in Ballots, v \in Values : Commit(s, b, v)
  \/ \E l \in Learners, m \in msgs : Learn(l, m)
  \/ Terminating

Spec == Init /\ [][Next]_vars

(* Safety properties *)
Agreement ==
  \A l1, l2 \in Learners : \A s \in Slots :
     (learned[l1][s] # None /\ learned[l2][s] # None)
        => learned[l1][s] = learned[l2][s]

Validity ==
  \A l \in Learners : \A s \in Slots :
     learned[l][s] # None =>
        \E pr \in proposed : pr.slot = s /\ pr.val = learned[l][s]

CommitConsistency ==
  \A m1, m2 \in msgs :
     (m1.type = "commit" /\ m2.type = "commit" /\ m1.slot = m2.slot)
        => m1.val = m2.val

Termination == <>AllDone

=============================================================================
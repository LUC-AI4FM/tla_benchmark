------------------------------ MODULE MultiPaxos ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Proposers, Acceptors, Quorums, Learners, Values, Slots, Ballots

ASSUME /\ Cardinality(Acceptors) >= 3
       /\ \A Q \in Quorums : Q \subseteq Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
       /\ Cardinality(Values) >= 2
       /\ Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

NoVote == [bal |-> -1, val |-> None]

VARIABLES msgs, pBallot, aBallot, aVoted, proposed, learned

vars == <<msgs, pBallot, aBallot, aVoted, proposed, learned>>

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
  /\ msgs = {}
  /\ pBallot = [p \in Proposers |-> -1]
  /\ aBallot = [a \in Acceptors |-> -1]
  /\ aVoted = [a \in Acceptors |-> [s \in Slots |-> NoVote]]
  /\ proposed = [s \in Slots |-> {}]
  /\ learned = [s \in Slots |-> {}]

-----------------------------------------------------------------------------
(* Proposer actions *)

Phase1a(p) ==
  \E b \in Ballots :
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ pBallot' = [pBallot EXCEPT ![p] = b]
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<aBallot, aVoted, proposed, learned>>

Phase2a(p, s, v) ==
  LET b == pBallot[p] IN
  /\ b # -1
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       LET M == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
       IN /\ \A a \in Q : \E m \in M : m.from = a
          /\ \/ \A m \in M : m.voted[s].bal = -1
             \/ \E m \in M :
                  /\ m.voted[s].bal # -1
                  /\ m.voted[s].val = v
                  /\ \A m2 \in M : m2.voted[s].bal <= m.voted[s].bal
  /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
  /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
  /\ UNCHANGED <<pBallot, aBallot, aVoted, learned>>

-----------------------------------------------------------------------------
(* Acceptor actions *)

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > aBallot[a]
    /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", from |-> a, bal |-> m.bal, voted |-> aVoted[a]])
    /\ UNCHANGED <<pBallot, aVoted, proposed, learned>>

Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= aBallot[a]
    /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
    /\ aVoted' = [aVoted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
    /\ Send([type |-> "2b", from |-> a, bal |-> m.bal, slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED <<pBallot, proposed, learned>>

-----------------------------------------------------------------------------
(* Learner actions *)

Learn(l, s, v) ==
  /\ v \notin learned[s]
  /\ \E b \in Ballots, Q \in Quorums :
       \A a \in Q :
         \E m \in msgs :
           /\ m.type = "2b"
           /\ m.from = a
           /\ m.bal = b
           /\ m.slot = s
           /\ m.val = v
  /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
  /\ UNCHANGED <<msgs, pBallot, aBallot, aVoted, proposed>>

-----------------------------------------------------------------------------
Next ==
  \/ \E p \in Proposers : Phase1a(p)
  \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
  \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
  \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

=============================================================================
---------------------------- MODULE MCMultiPaxos ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Proposers, Acceptors, Quorums, Learners, Values, Slots, Ballots

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

ConstBallots == 0..2

SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

VARIABLES msgs, maxBal, votes, learned

vars == <<msgs, maxBal, votes, learned>>

NoBallot == -1

VoteSet == [slot : Slots, bal : Ballots, val : Values]

Messages ==
         [type : {"1a"}, from : Proposers, bal : Ballots]
    \cup [type : {"1b"}, from : Acceptors, bal : Ballots, votes : SUBSET VoteSet]
    \cup [type : {"2a"}, from : Proposers, bal : Ballots, slot : Slots, val : Values]
    \cup [type : {"2b"}, from : Acceptors, bal : Ballots, slot : Slots, val : Values]

Send(m) == msgs' = msgs \cup {m}

Init ==
    /\ msgs = {}
    /\ maxBal = [a \in Acceptors |-> NoBallot]
    /\ votes = [a \in Acceptors |-> {}]
    /\ learned = [l \in Learners |-> {}]

Phase1a(p, b) ==
    /\ ~\E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", from |-> p, bal |-> b])
    /\ UNCHANGED <<maxBal, votes, learned>>

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", from |-> a, bal |-> m.bal, votes |-> votes[a]])
        /\ UNCHANGED <<votes, learned>>

Phase2a(p, b, s, v) ==
    /\ \E m \in msgs : m.type = "1a" /\ m.bal = b /\ m.from = p
    /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET M == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
             V == {vt \in UNION {m.votes : m \in M} : vt.slot = s}
         IN  /\ \A a \in Q : \E m \in M : m.from = a
             /\ \/ V = {}
                \/ \E vt \in V : /\ vt.val = v
                                 /\ \A w \in V : w.bal <= vt.bal
    /\ Send([type |-> "2a", from |-> p, bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<maxBal, votes, learned>>

Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ votes' = [votes EXCEPT ![a] =
                        {vt \in votes[a] : vt.slot # m.slot}
                          \cup {[slot |-> m.slot, bal |-> m.bal, val |-> m.val]}]
        /\ Send([type |-> "2b", from |-> a, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED learned

Learn(l, s, v) ==
    /\ \E b \in Ballots, Q \in Quorums :
         \A a \in Q : \E m \in msgs : /\ m.type = "2b"
                                      /\ m.from = a
                                      /\ m.bal = b
                                      /\ m.slot = s
                                      /\ m.val = v
    /\ learned' = [learned EXCEPT ![l] = @ \cup {<<s, v>>}]
    /\ UNCHANGED <<msgs, maxBal, votes>>

Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
    \/ \E p \in Proposers, b \in Ballots, s \in Slots, v \in Values :
          Phase2a(p, b, s, v)
    \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Acceptors -> Ballots \cup {NoBallot}]
    /\ votes \in [Acceptors -> SUBSET VoteSet]
    /\ learned \in [Learners -> SUBSET (Slots \X Values)]

NontrivialityInv ==
    \A l \in Learners : \A pr \in learned[l] :
        /\ pr[2] \in Values
        /\ \E m \in msgs : /\ m.type = "2a"
                           /\ m.slot = pr[1]
                           /\ m.val = pr[2]

ConsistencyInv ==
    \A l1, l2 \in Learners : \A p1 \in learned[l1], p2 \in learned[l2] :
        p1[1] = p2[1] => p1[2] = p2[2]

Chosen(s) == {v \in Values : \E l \in Learners : <<s, v>> \in learned[l]}

ConsensusSpec ==
    /\ \A s \in Slots : Chosen(s) = {}
    /\ [][\A s \in Slots :
            /\ Cardinality(Chosen(s)') <= 1
            /\ Chosen(s) # {} => Chosen(s)' = Chosen(s)]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []ConsistencyInv
=============================================================================
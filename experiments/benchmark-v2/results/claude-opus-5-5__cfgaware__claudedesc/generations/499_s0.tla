---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Proposers, Acceptors, Quorums, Learners, Values, Slots, Ballots

ConstBallots == {0, 1}

SymmetricPerms ==
    Permutations(Proposers) \cup Permutations(Acceptors) \cup
    Permutations(Learners)  \cup Permutations(Values)    \cup
    Permutations(Slots)

ASSUME /\ \A Q \in Quorums : Q \subseteq Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == -1

VARIABLES msgs,     \* set of all messages sent
          pBal,     \* proposer state: ballot currently led by each proposer
          maxBal,   \* acceptor state: highest ballot promised
          votes,    \* acceptor state: set of <<ballot, slot, value>> votes cast
          learned   \* learner state: set of <<slot, value>> learned

vars == <<msgs, pBal, maxBal, votes, learned>>

VoteTriples == Ballots \X Slots \X Values

Msgs1a == [type : {"1a"}, from : Proposers, bal : Ballots]
Msgs1b == [type : {"1b"}, from : Acceptors, bal : Ballots, votes : SUBSET VoteTriples]
Msgs2a == [type : {"2a"}, from : Proposers, bal : Ballots, slot : Slots, val : Values]
Msgs2b == [type : {"2b"}, from : Acceptors, bal : Ballots, slot : Slots, val : Values]

Messages == Msgs1a \cup Msgs1b \cup Msgs2a \cup Msgs2b

TypeOK ==
    /\ msgs \subseteq Messages
    /\ pBal \in [Proposers -> Ballots \cup {None}]
    /\ maxBal \in [Acceptors -> Ballots \cup {None}]
    /\ votes \in [Acceptors -> SUBSET VoteTriples]
    /\ learned \in [Learners -> SUBSET (Slots \X Values)]

-----------------------------------------------------------------------------
(* Helper predicates *)

ProposedIn(v, b, s) ==
    \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s /\ m.val = v

Proposed(v, s) == \E b \in Ballots : ProposedIn(v, b, s)

VotedForIn(a, v, b, s) ==
    \E m \in msgs : /\ m.type = "2b" /\ m.from = a
                    /\ m.bal = b /\ m.slot = s /\ m.val = v

CannotVoteAt(a, b) ==
    /\ maxBal[a] > b
    /\ \A s \in Slots : \A v \in Values : ~VotedForIn(a, v, b, s)

ChosenIn(v, b, s) ==
    \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b, s)

Chosen(v, s) == \E b \in Ballots : ChosenIn(v, b, s)

-----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ pBal = [p \in Proposers |-> None]
    /\ maxBal = [a \in Acceptors |-> None]
    /\ votes = [a \in Acceptors |-> {}]
    /\ learned = [l \in Learners |-> {}]

Send(m) == msgs' = msgs \cup {m}

Phase1a(p, b) ==
    /\ b > pBal[p]
    /\ ~\E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", from |-> p, bal |-> b])
    /\ pBal' = [pBal EXCEPT ![p] = b]
    /\ UNCHANGED <<maxBal, votes, learned>>

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", from |-> a, bal |-> m.bal, votes |-> votes[a]])
        /\ UNCHANGED <<pBal, votes, learned>>

Phase2a(p, s, v) ==
    LET b == pBal[p] IN
    /\ b # None
    /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
             VS  == {t \in UNION {m.votes : m \in Q1b} : t[2] = s}
         IN /\ \A a \in Q : \E m \in Q1b : m.from = a
            /\ \/ VS = {}
               \/ \E t \in VS : /\ t[3] = v
                                /\ \A t2 \in VS : t2[1] <= t[1]
    /\ Send([type |-> "2a", from |-> p, bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<pBal, maxBal, votes, learned>>

Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ votes' = [votes EXCEPT ![a] = @ \cup {<<m.bal, m.slot, m.val>>}]
        /\ Send([type |-> "2b", from |-> a, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<pBal, learned>>

Learn(l, s, v) ==
    /\ Chosen(v, s)
    /\ learned' = [learned EXCEPT ![l] = @ \cup {<<s, v>>}]
    /\ UNCHANGED <<msgs, pBal, maxBal, votes>>

Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

NontrivialityInv ==
    \A l \in Learners : \A t \in learned[l] : Proposed(t[2], t[1])

ConsistencyInv ==
    \A l1, l2 \in Learners :
        \A t1 \in learned[l1], t2 \in learned[l2] :
            t1[1] = t2[1] => t1[2] = t2[2]

(* Refinement to an abstract ConsensusMulti specification *)
LearnedVals(s) == {v \in Values : \E l \in Learners : <<s, v>> \in learned[l]}

chosenM == [s \in Slots |-> LearnedVals(s)]

CMInit == \A s \in Slots : chosenM[s] = {}

CMNext ==
    \E s \in Slots, v \in Values :
        /\ chosenM[s] = {}
        /\ chosenM' = [chosenM EXCEPT ![s] = {v}]

ConsensusSpec == CMInit /\ [][CMNext]_chosenM

=============================================================================
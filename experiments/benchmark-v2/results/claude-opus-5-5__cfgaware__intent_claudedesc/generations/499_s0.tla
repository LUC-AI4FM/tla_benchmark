---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Proposers, Acceptors, Quorums, Learners, Values, Slots, Ballots

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

\* Concrete finite set of ballots for model checking
ConstBallots == 0..2

\* Symmetry set for model checking
SymmetricPerms == Permutations(Acceptors) \cup Permutations(Values)

VARIABLES
    maxBal,     \* maxBal[a]       : highest ballot acceptor a has promised (shared over slots)
    maxVBal,    \* maxVBal[a][s]   : ballot of the latest vote of a in slot s (-1 if none)
    maxVal,     \* maxVal[a][s]    : value of the latest vote of a in slot s (None if none)
    msgs,       \* set of messages sent
    proposed,   \* proposed[s]     : set of values proposed for slot s
    learned     \* learned[l][s]   : set of values learned by l for slot s

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, learned>>

Message ==
         [type : {"1a"}, from : Proposers, bal : Ballots]
    \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
          mbal : [Slots -> Ballots \cup {-1}],
          mval : [Slots -> Values \cup {None}]]
    \cup [type : {"2a"}, from : Proposers, bal : Ballots, slot : Slots, val : Values]
    \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

TypeOK ==
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> [Slots -> Ballots \cup {-1}]]
    /\ maxVal \in [Acceptors -> [Slots -> Values \cup {None}]]
    /\ msgs \subseteq Message
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Learners -> [Slots -> SUBSET Values]]

Init ==
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> [s \in Slots |-> -1]]
    /\ maxVal = [a \in Acceptors |-> [s \in Slots |-> None]]
    /\ msgs = {}
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [l \in Learners |-> [s \in Slots |-> {}]]

Send(m) == msgs' = msgs \cup {m}

\* A client/proposer proposes value v for slot s
Propose(s, v) ==
    /\ v \notin proposed[s]
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, learned>>

\* Proposer p starts ballot b (prepare for all slots at once)
Phase1a(p, b) ==
    /\ Send([type |-> "1a", from |-> p, bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, learned>>

\* Acceptor a promises ballot b, reporting its votes in every slot
Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
        /\ UNCHANGED <<maxVBal, maxVal, proposed, learned>>

\* Proposer p, leader of ballot b, proposes v in slot s
Phase2a(p, b, s, v) ==
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
        LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ /\ \A m \in Q1b : m.mbal[s] = -1
                  /\ v \in proposed[s]
               \/ \E c \in Q1b :
                     /\ c.mbal[s] # -1
                     /\ c.mval[s] = v
                     /\ \A d \in Q1b : d.mbal[s] <= c.mbal[s]
    /\ Send([type |-> "2a", from |-> p, bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, learned>>

\* Acceptor a votes for a 2a proposal
Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a][m.slot] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<proposed, learned>>

\* Learner l learns v in slot s once a quorum voted for it in one ballot
Learn(l, s, v) ==
    /\ \E b \in Ballots, Q \in Quorums :
         \A a \in Q : [type |-> "2b", acc |-> a, bal |-> b,
                       slot |-> s, val |-> v] \in msgs
    /\ v \notin learned[l][s]
    /\ learned' = [learned EXCEPT ![l][s] = @ \cup {v}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposed>>

Next ==
    \/ \E s \in Slots, v \in Values : Propose(s, v)
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, b \in Ballots, s \in Slots, v \in Values :
          Phase2a(p, b, s, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

NontrivialityInv ==
    \A l \in Learners, s \in Slots : learned[l][s] \subseteq proposed[s]

ConsistencyInv ==
    \A s \in Slots : \A l1, l2 \in Learners :
        \A v1 \in learned[l1][s], v2 \in learned[l2][s] : v1 = v2

StabilityProp ==
    \A l \in Learners, s \in Slots, v \in Values :
        [](v \in learned[l][s] => [](v \in learned[l][s]))

-----------------------------------------------------------------------------
\* Abstract multi-slot consensus specification (refinement target)

chosenBar == [s \in Slots |-> UNION {learned[l][s] : l \in Learners}]

ConsInit ==
    /\ proposed = [s \in Slots |-> {}]
    /\ chosenBar = [s \in Slots |-> {}]

ConsPropose(s, v) ==
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ chosenBar' = chosenBar

ConsChoose(s, v) ==
    /\ chosenBar[s] = {}
    /\ v \in proposed[s]
    /\ chosenBar' = [chosenBar EXCEPT ![s] = {v}]
    /\ proposed' = proposed

ConsNext ==
    \E s \in Slots, v \in Values : ConsPropose(s, v) \/ ConsChoose(s, v)

ConsensusSpec == ConsInit /\ [][ConsNext]_<<proposed, chosenBar>>

=============================================================================
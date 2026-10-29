---------------------------- MODULE MCMultiPaxos ----------------------------
(***************************************************************************)
(* Model-checking configuration for a Multi-Paxos consensus specification. *)
(* Two proposers, three acceptors (three majority quorums), one learner,   *)
(* two values, two slots, and ballots restricted to {0, 1}.  Symmetry      *)
(* reduction is applied over all finite sets of model values.              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS p1, p2,          \* proposers
          a1, a2, a3,      \* acceptors
          l1,              \* learner
          v1, v2,          \* values
          s1, s2,          \* slots
          None             \* model value distinct from all values

-----------------------------------------------------------------------------
(* Model instantiation *)

Proposers == {p1, p2}
Acceptors == {a1, a2, a3}
Learners  == {l1}
Values    == {v1, v2}
Slots     == {s1, s2}
Ballots   == {0, 1}
Quorums   == {{a1, a2}, {a1, a3}, {a2, a3}}

Symmetry ==
    Permutations(Proposers) \cup Permutations(Acceptors) \cup
    Permutations(Learners)  \cup Permutations(Values)    \cup
    Permutations(Slots)

ASSUME /\ \A Q \in Quorums : Q \subseteq Acceptors
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
       /\ None \notin Values

-----------------------------------------------------------------------------
(* Messages *)

Votes == [Slots -> [bal : Ballots \cup {-1}, val : Values \cup {None}]]

Msg1a == [type : {"1a"}, bal : Ballots, from : Proposers]
Msg1b == [type : {"1b"}, bal : Ballots, acc : Acceptors, votes : Votes]
Msg2a == [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
Msg2b == [type : {"2b"}, bal : Ballots, slot : Slots, val : Values,
          acc : Acceptors]

Messages == Msg1a \cup Msg1b \cup Msg2a \cup Msg2b

VARIABLES msgs,      \* set of all messages sent
          pBal,      \* pBal[p]    : current ballot of proposer p (-1 = none)
          maxBal,    \* maxBal[a]  : highest ballot acceptor a has joined
          maxVBal,   \* maxVBal[a][s] : ballot of a's last vote in slot s
          maxVal,    \* maxVal[a][s]  : value of a's last vote in slot s
          learned    \* learned[l] : set of <<slot, value>> pairs learned

vars == <<msgs, pBal, maxBal, maxVBal, maxVal, learned>>

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* Helper predicates *)

Proposed(v, b, s) ==
    [type |-> "2a", bal |-> b, slot |-> s, val |-> v] \in msgs

ProposedAny(v, s) == \E b \in Ballots : Proposed(v, b, s)

VotedFor(a, b, s, v) ==
    [type |-> "2b", bal |-> b, slot |-> s, val |-> v, acc |-> a] \in msgs

CannotVoteAt(a, b) == maxBal[a] > b

ChosenAt(b, s, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, s, v)

ChosenIn(s, v) == \E b \in Ballots : ChosenAt(b, s, v)

Chosen(s) == {v \in Values : ChosenIn(s, v)}

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ msgs \subseteq Messages
    /\ pBal \in [Proposers -> Ballots \cup {-1}]
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> [Slots -> Ballots \cup {-1}]]
    /\ maxVal \in [Acceptors -> [Slots -> Values \cup {None}]]
    /\ learned \in [Learners -> SUBSET (Slots \X Values)]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ msgs = {}
    /\ pBal = [p \in Proposers |-> -1]
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> [s \in Slots |-> -1]]
    /\ maxVal = [a \in Acceptors |-> [s \in Slots |-> None]]
    /\ learned = [l \in Learners |-> {}]

-----------------------------------------------------------------------------
(* Actions *)

\* Proposer p starts a fresh, globally unused ballot b.
Phase1a(p, b) ==
    /\ b > pBal[p]
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ pBal' = [pBal EXCEPT ![p] = b]
    /\ Send([type |-> "1a", bal |-> b, from |-> p])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, learned>>

\* Acceptor a promises ballot m.bal, reporting its last votes for all slots.
Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type  |-> "1b", bal |-> m.bal, acc |-> a,
                 votes |-> [s \in Slots |->
                              [bal |-> maxVBal[a][s], val |-> maxVal[a][s]]]])
        /\ UNCHANGED <<pBal, maxVBal, maxVal, learned>>

\* Proposer p proposes value v for slot s in its current ballot.
Phase2a(p, s, v) ==
    LET b == pBal[p] IN
    /\ b # -1
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET Q1b  == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
             Q1bv == {m \in Q1b : m.votes[s].bal >= 0}
         IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
             /\ \/ Q1bv = {}
                \/ \E m \in Q1bv :
                     /\ m.votes[s].val = v
                     /\ \A mm \in Q1bv : mm.votes[s].bal <= m.votes[s].bal
    /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<pBal, maxBal, maxVBal, maxVal, learned>>

\* Acceptor a votes for a proposal it has not promised to ignore.
Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
        /\ maxVal'  = [maxVal  EXCEPT ![a][m.slot] = m.val]
        /\ Send([type |-> "2b", bal |-> m.bal, slot |-> m.slot,
                 val |-> m.val, acc |-> a])
        /\ UNCHANGED <<pBal, learned>>

\* Learner l learns v for slot s once a quorum voted for it in some ballot.
Learn(l, s, v) ==
    /\ \E b \in Ballots : ChosenAt(b, s, v)
    /\ learned' = [learned EXCEPT ![l] = @ \cup {<<s, v>>}]
    /\ UNCHANGED <<msgs, pBal, maxBal, maxVBal, maxVal>>

Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E a \in Acceptors : Phase1b(a)
    \/ \E p \in Proposers, s \in Slots, v \in Values : Phase2a(p, s, v)
    \/ \E a \in Acceptors : Phase2b(a)
    \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

Nontriviality ==
    \A l \in Learners : \A sv \in learned[l] : ProposedAny(sv[2], sv[1])

Consistency ==
    \A l, l2 \in Learners, s \in Slots, v, w \in Values :
        (<<s, v>> \in learned[l] /\ <<s, w>> \in learned[l2]) => v = w

-----------------------------------------------------------------------------
(* Refinement to ConsensusMulti *)

chosenBar == [s \in Slots |->
                {v \in Values : \E l \in Learners : <<s, v>> \in learned[l]}]

CInit == chosenBar = [s \in Slots |-> {}]

CNext ==
    \E s \in Slots, v \in Values :
        /\ chosenBar[s] = {}
        /\ chosenBar' = [chosenBar EXCEPT ![s] = {v}]

ConsensusMultiSpec == CInit /\ [][CNext]_chosenBar

CNontriviality == \A s \in Slots : chosenBar[s] \subseteq Values

CConsistency == \A s \in Slots : Cardinality(chosenBar[s]) <= 1

CStability ==
    \A s \in Slots, v \in Values :
        [](v \in chosenBar[s] => [](v \in chosenBar[s]))

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
THEOREM Spec => ConsensusMultiSpec

(***************************************************************************)
(* TLC configuration (deadlock checking disabled):                         *)
(*   SPECIFICATION Spec                                                    *)
(*   SYMMETRY Symmetry                                                     *)
(*   INVARIANTS TypeOK Nontriviality Consistency                           *)
(*   PROPERTIES ConsensusMultiSpec CStability                              *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
=============================================================================
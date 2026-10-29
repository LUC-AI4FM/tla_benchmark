------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ConstBallots == 0..2

SymmetricPerms ==
    Permutations(Replicas) \cup Permutations(Values) \cup Permutations(Slots)

NullVal == CHOOSE x : x \notin Values

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

VARIABLES msgs,       \* set of all messages ever sent
          maxBal,     \* acceptor: highest ballot promised
          maxVBal,    \* acceptor: per slot, ballot of last vote
          maxVal,     \* acceptor: per slot, value of last vote
          proposed,   \* per slot, set of proposed values
          learned     \* per slot, set of learned values

vars == <<msgs, maxBal, maxVBal, maxVal, proposed, learned>>

BallotOrNone == Ballots \cup {-1}
ValueOrNone  == Values \cup {NullVal}

VoteRec == [bal : BallotOrNone, val : ValueOrNone]

Messages ==
         [type : {"1a"}, from : Replicas, bal : Ballots]
    \cup [type : {"1b"}, from : Replicas, bal : Ballots, voted : [Slots -> VoteRec]]
    \cup [type : {"2a"}, from : Replicas, bal : Ballots, slot : Slots, val : Values]
    \cup [type : {"2b"}, from : Replicas, bal : Ballots, slot : Slots, val : Values]

TypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Replicas -> BallotOrNone]
    /\ maxVBal \in [Replicas -> [Slots -> BallotOrNone]]
    /\ maxVal \in [Replicas -> [Slots -> ValueOrNone]]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Slots -> SUBSET Values]

Init ==
    /\ msgs = {}
    /\ maxBal = [r \in Replicas |-> -1]
    /\ maxVBal = [r \in Replicas |-> [s \in Slots |-> -1]]
    /\ maxVal = [r \in Replicas |-> [s \in Slots |-> NullVal]]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [s \in Slots |-> {}]

Send(m) == msgs' = msgs \cup {m}

\* A client proposes value v for slot s.
Propose(s, v) ==
    /\ v \notin proposed[s]
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, maxBal, maxVBal, maxVal, learned>>

\* Prepare: replica r starts ballot b (each ballot owned by at most one replica).
Phase1a(r, b) ==
    /\ ~\E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", from |-> r, bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, learned>>

\* Promise: acceptor r replies with its accepted values for all slots.
Phase1b(r, b) ==
    /\ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ b > maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = b]
    /\ Send([type |-> "1b", from |-> r, bal |-> b,
             voted |-> [s \in Slots |-> [bal |-> maxVBal[r][s],
                                         val |-> maxVal[r][s]]]])
    /\ UNCHANGED <<maxVBal, maxVal, proposed, learned>>

\* Accept request: leader r of ballot b proposes v for slot s after
\* gathering promises from a quorum.
Phase2a(r, b, s, v) ==
    /\ [type |-> "1a", from |-> r, bal |-> b] \in msgs
    /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET S == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
             votes == {m \in S : m.voted[s].bal # -1}
         IN  /\ \A q \in Q : \E m \in S : m.from = q
             /\ IF votes = {}
                  THEN v \in proposed[s]
                  ELSE \E m \in votes :
                         /\ m.voted[s].val = v
                         /\ \A m2 \in votes : m2.voted[s].bal <= m.voted[s].bal
    /\ Send([type |-> "2a", from |-> r, bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, learned>>

\* Accept: acceptor r accepts value v for slot s at ballot b.
Phase2b(r, b, s, v) ==
    /\ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s /\ m.val = v
    /\ b >= maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![r][s] = b]
    /\ maxVal' = [maxVal EXCEPT ![r][s] = v]
    /\ Send([type |-> "2b", from |-> r, bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<proposed, learned>>

\* Learn: a quorum accepted v for slot s in the same ballot.
Learn(s, v) ==
    /\ \E b \in Ballots, Q \in Quorums :
         \A q \in Q :
           [type |-> "2b", from |-> q, bal |-> b, slot |-> s, val |-> v] \in msgs
    /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, maxBal, maxVBal, maxVal, proposed>>

Next ==
    \/ \E s \in Slots, v \in Values : Propose(s, v)
    \/ \E r \in Replicas, b \in Ballots : Phase1a(r, b)
    \/ \E r \in Replicas, b \in Ballots : Phase1b(r, b)
    \/ \E r \in Replicas, b \in Ballots, s \in Slots, v \in Values : Phase2a(r, b, s, v)
    \/ \E r \in Replicas, b \in Ballots, s \in Slots, v \in Values : Phase2b(r, b, s, v)
    \/ \E s \in Slots, v \in Values : Learn(s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Correctness properties

NontrivialityInv == \A s \in Slots : learned[s] \subseteq proposed[s]

ConsistencyInv == \A s \in Slots : Cardinality(learned[s]) <= 1

StabilityProp ==
    \A s \in Slots, v \in Values :
        [](v \in learned[s] => [](v \in learned[s]))

\* Abstract multi-slot consensus: each slot learns at most one proposed
\* value, and decisions never change.
AbstractInit ==
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [s \in Slots |-> {}]

AbstractNext ==
    \/ \E s \in Slots, v \in Values :
         /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
         /\ UNCHANGED learned
    \/ \E s \in Slots, v \in Values :
         /\ learned[s] = {}
         /\ v \in proposed[s]
         /\ learned' = [learned EXCEPT ![s] = {v}]
         /\ UNCHANGED proposed

AbstractSpec == AbstractInit /\ [][AbstractNext]_<<proposed, learned>>

RefinementProp == AbstractSpec

=============================================================================
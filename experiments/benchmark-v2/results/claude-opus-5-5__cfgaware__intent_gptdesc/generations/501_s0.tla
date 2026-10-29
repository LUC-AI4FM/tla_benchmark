------------------------------ MODULE MultiPaxos ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ConstBallots == 0..2

SymmetricPerms == Permutations(Replicas) \cup Permutations(Values)

VARIABLES
    msgs,       \* set of all messages ever sent (delivery is nondeterministic; loss = never delivered)
    maxBal,     \* maxBal[r]: highest ballot replica r has promised/accepted (-1 = none)
    lVotes,     \* lVotes[r]: persistent set of votes [slot, bal, val] cast by replica r
    proposed,   \* proposed[s]: set of values proposed for slot s
    learned     \* learned[s]: set of values learned for slot s

vars == <<msgs, maxBal, lVotes, proposed, learned>>

-------------------------------------------------------------------------------

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

VoteRec == [slot : Slots, bal : Ballots, val : Values]

Messages ==
         [type : {"Prepare"}, bal : Ballots]
    \cup [type : {"PrepareReply"}, src : Replicas, bal : Ballots, votes : SUBSET VoteRec]
    \cup [type : {"Accept"}, slot : Slots, bal : Ballots, val : Values]
    \cup [type : {"AcceptReply"}, src : Replicas, slot : Slots, bal : Ballots, val : Values]

Send(m) == msgs' = msgs \cup {m}

-------------------------------------------------------------------------------

Init ==
    /\ msgs = {}
    /\ maxBal = [r \in Replicas |-> -1]
    /\ lVotes = [r \in Replicas |-> {}]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [s \in Slots |-> {}]

\* A client/replica proposes value v for slot s.
Propose(s, v) ==
    /\ v \notin proposed[s]
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, maxBal, lVotes, learned>>

\* Phase 1a: a leader starts ballot b (covering all slots).
Prepare(b) ==
    /\ Send([type |-> "Prepare", bal |-> b])
    /\ UNCHANGED <<maxBal, lVotes, proposed, learned>>

\* Phase 1b: replica r promises ballot b and reports all its prior votes.
ReceivePrepare(r, m) ==
    /\ m.type = "Prepare"
    /\ m.bal > maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
    /\ Send([type |-> "PrepareReply", src |-> r, bal |-> m.bal, votes |-> lVotes[r]])
    /\ UNCHANGED <<lVotes, proposed, learned>>

\* Phase 2a: leader of ballot b proposes value v for slot s, given a quorum of promises.
SendAccept(b, s, v) ==
    /\ ~ \E m \in msgs : m.type = "Accept" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET replies == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b /\ m.src \in Q}
             sv == {vt \in UNION {m.votes : m \in replies} : vt.slot = s}
         IN  /\ \A q \in Q : \E m \in replies : m.src = q
             /\ \/ /\ sv = {}
                   /\ v \in proposed[s]
                \/ \E vt \in sv : /\ vt.val = v
                                  /\ \A w \in sv : w.bal <= vt.bal
    /\ Send([type |-> "Accept", slot |-> s, bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBal, lVotes, proposed, learned>>

\* Phase 2b: replica r accepts (votes for) a proposal.
ReceiveAccept(r, m) ==
    /\ m.type = "Accept"
    /\ m.bal >= maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
    /\ lVotes' = [lVotes EXCEPT ![r] = @ \cup {[slot |-> m.slot, bal |-> m.bal, val |-> m.val]}]
    /\ Send([type |-> "AcceptReply", src |-> r, slot |-> m.slot, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED <<proposed, learned>>

\* Learner: learns v for slot s once a quorum accepted it in the same ballot.
Learn(s, b, v) ==
    /\ \E Q \in Quorums :
         \A q \in Q : \E m \in msgs : /\ m.type = "AcceptReply"
                                      /\ m.src = q
                                      /\ m.slot = s
                                      /\ m.bal = b
                                      /\ m.val = v
    /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED <<msgs, maxBal, lVotes, proposed>>

Next ==
    \/ \E s \in Slots, v \in Values : Propose(s, v)
    \/ \E b \in Ballots : Prepare(b)
    \/ \E r \in Replicas, m \in msgs : ReceivePrepare(r, m)
    \/ \E b \in Ballots, s \in Slots, v \in Values : SendAccept(b, s, v)
    \/ \E r \in Replicas, m \in msgs : ReceiveAccept(r, m)
    \/ \E s \in Slots, b \in Ballots, v \in Values : Learn(s, b, v)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
\* Correctness properties

TypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Replicas -> Ballots \cup {-1}]
    /\ lVotes \in [Replicas -> SUBSET VoteRec]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Slots -> SUBSET Values]

NontrivialityInv ==
    \A s \in Slots : learned[s] \subseteq proposed[s]

ConsistencyInv ==
    \A s \in Slots : Cardinality(learned[s]) <= 1

ReplyValidityInv ==
    \A m \in msgs :
        m.type = "PrepareReply" =>
            /\ m.votes \subseteq lVotes[m.src]
            /\ \A vt \in m.votes : vt.bal < m.bal

StabilityProp ==
    \A s \in Slots, v \in Values :
        [](v \in learned[s] => [](v \in learned[s]))

StabilityAction ==
    [][\A s \in Slots : learned[s] \subseteq learned'[s]]_vars

===============================================================================
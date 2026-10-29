------------------------------ MODULE MultiPaxos ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Proposers,   \* finite set of proposer ids
          Acceptors,   \* finite set of acceptor ids
          Learners,    \* finite set of learner ids
          Quorums,     \* set of subsets of Acceptors
          Slots,       \* finite set of ordered slots (instances)
          Ballots,     \* finite set of ballot numbers (naturals)
          Values       \* finite set of proposable values

ASSUME BallotsAreNat == Ballots \subseteq Nat
ASSUME QuorumsAreSubsets == Quorums \subseteq SUBSET Acceptors
ASSUME QuorumsNonEmpty == \A Q \in Quorums : Q # {}

(* Safety property (4): valid quorum intersection, assumed as a parameter. *)
ASSUME QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values
NoBallot == -1
NoVote == [bal |-> NoBallot, val |-> None]

VARIABLES
    pBallot,   \* pBallot[p]  : current ballot of proposer p (-1 if none yet)
    aBallot,   \* aBallot[a]  : highest ballot promised/seen by acceptor a
    aVoted,    \* aVoted[a][s]: highest accepted [bal, val] for slot s at a
    msgs,      \* set of all messages ever sent
    proposed,  \* set of <<slot, ballot, value>> proposed by proposers
    learned    \* learned[l][s] : value learned for slot s by l (or None)

vars == <<pBallot, aBallot, aVoted, msgs, proposed, learned>>

VoteRec == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]

Messages ==
       [type : {"1a"}, bal : Ballots, from : Proposers]
  \cup [type : {"1b"}, bal : Ballots, acc : Acceptors, voted : [Slots -> VoteRec]]
  \cup [type : {"2a"}, bal : Ballots, slot : Slots, val : Values, from : Proposers]
  \cup [type : {"2b"}, bal : Ballots, slot : Slots, val : Values, acc : Acceptors]

TypeOK ==
  /\ pBallot \in [Proposers -> Ballots \cup {NoBallot}]
  /\ aBallot \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ aVoted \in [Acceptors -> [Slots -> VoteRec]]
  /\ msgs \subseteq Messages
  /\ proposed \subseteq (Slots \X Ballots \X Values)
  /\ learned \in [Learners -> [Slots -> Values \cup {None}]]

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ pBallot = [p \in Proposers |-> NoBallot]
  /\ aBallot = [a \in Acceptors |-> NoBallot]
  /\ aVoted = [a \in Acceptors |-> [s \in Slots |-> NoVote]]
  /\ msgs = {}
  /\ proposed = {}
  /\ learned = [l \in Learners |-> [s \in Slots |-> None]]

-----------------------------------------------------------------------------
(* Phase 1a: proposer picks a fresh, higher ballot and broadcasts prepare.   *)
Prepare(p, b) ==
  /\ b > pBallot[p]
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b   \* ballots are distinct
  /\ pBallot' = [pBallot EXCEPT ![p] = b]
  /\ Send([type |-> "1a", bal |-> b, from |-> p])
  /\ UNCHANGED <<aBallot, aVoted, proposed, learned>>

(* Phase 1b: acceptor promises a strictly higher ballot, reporting all its   *)
(* previously accepted (ballot, value) pairs for every slot (aggregated).    *)
Promise(a, m) ==
  /\ m \in msgs
  /\ m.type = "1a"
  /\ m.bal > aBallot[a]
  /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
  /\ Send([type |-> "1b", bal |-> m.bal, acc |-> a, voted |-> aVoted[a]])
  /\ UNCHANGED <<pBallot, aVoted, proposed, learned>>

(* Phase 2a: with promises from a quorum for its current ballot, proposer    *)
(* proposes for slot s the value of highest ballot reported, or any value.   *)
Propose(p, s, v) ==
  LET b == pBallot[p] IN
  /\ b # NoBallot
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
           vs  == {m.voted[s] : m \in Q1b}
           hb  == CHOOSE x \in vs : \A y \in vs : y.bal <= x.bal
       IN /\ \A a \in Q : \E m \in Q1b : m.acc = a
          /\ IF hb.bal = NoBallot THEN v \in Values ELSE v = hb.val
  /\ proposed' = proposed \cup {<<s, b, v>>}
  /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v, from |-> p])
  /\ UNCHANGED <<pBallot, aBallot, aVoted, learned>>

(* Phase 2b: acceptor accepts if the ballot is not lower than its promise.   *)
Accept(a, m) ==
  /\ m \in msgs
  /\ m.type = "2a"
  /\ m.bal >= aBallot[a]
  /\ aBallot' = [aBallot EXCEPT ![a] = m.bal]
  /\ aVoted' = [aVoted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
  /\ Send([type |-> "2b", bal |-> m.bal, slot |-> m.slot,
           val |-> m.val, acc |-> a])
  /\ UNCHANGED <<pBallot, proposed, learned>>

(* Learner learns v for slot s once a full quorum accepted it in a ballot.  *)
Learn(l, s, v) ==
  /\ learned[l][s] = None
  /\ \E b \in Ballots, Q \in Quorums :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "2b" /\ m.bal = b /\ m.slot = s
          /\ m.val = v /\ m.acc = a
  /\ learned' = [learned EXCEPT ![l][s] = v]
  /\ UNCHANGED <<pBallot, aBallot, aVoted, msgs, proposed>>

Next ==
  \/ \E p \in Proposers, b \in Ballots : Prepare(p, b)
  \/ \E a \in Acceptors, m \in msgs : Promise(a, m)
  \/ \E p \in Proposers, s \in Slots, v \in Values : Propose(p, s, v)
  \/ \E a \in Acceptors, m \in msgs : Accept(a, m)
  \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                         *)

Chosen(s, v) ==
  \E b \in Ballots, Q \in Quorums :
    \A a \in Q : \E m \in msgs :
      m.type = "2b" /\ m.bal = b /\ m.slot = s /\ m.val = v /\ m.acc = a

(* (1) Agreement: at most one value is chosen/learned per slot. *)
Agreement ==
  /\ \A s \in Slots : \A v1, v2 \in Values :
        (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2
  /\ \A s \in Slots : \A l1, l2 \in Learners :
        (learned[l1][s] # None /\ learned[l2][s] # None)
          => learned[l1][s] = learned[l2][s]

(* (2) Integrity: a learned/chosen value was proposed by some proposer. *)
Integrity ==
  /\ \A l \in Learners, s \in Slots :
        learned[l][s] # None =>
          \E b \in Ballots : <<s, b, learned[l][s]>> \in proposed
  /\ \A s \in Slots, v \in Values :
        Chosen(s, v) => \E b \in Ballots : <<s, b, v>> \in proposed

(* (3) Monotonic ballots: acceptors never decrease their promised ballot. *)
MonotonicBallots ==
  [][\A a \in Acceptors : aBallot'[a] >= aBallot[a]]_vars

(* (4) Quorum intersection as a checkable state predicate as well. *)
QuorumsIntersect == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Safety == TypeOK /\ Agreement /\ Integrity

-----------------------------------------------------------------------------
(* Liveness (under eventual reliable communication and a stable leader).    *)
(* Fairness: a majority/quorum of acceptors keeps responding, messages are   *)
(* eventually delivered, and learners eventually learn.                      *)

Fairness ==
  /\ \A a \in Acceptors : WF_vars(\E m \in msgs : Promise(a, m))
  /\ \A a \in Acceptors : WF_vars(\E m \in msgs : Accept(a, m))
  /\ \A l \in Learners, s \in Slots, v \in Values : WF_vars(Learn(l, s, v))
  /\ \A p \in Proposers, s \in Slots :
        WF_vars(\E v \in Values : Propose(p, s, v))

FairSpec == Spec /\ Fairness

(* Stable leader: eventually only one proposer acquires new ballots. *)
StableLeader ==
  \E p \in Proposers :
    <>[][\A q \in Proposers \ {p} : pBallot'[q] = pBallot[q]]_vars

(* Progress: once a value is proposed for a slot, some value is eventually  *)
(* learned for that slot by every learner.                                   *)
Progress ==
  \A s \in Slots :
    (\E b \in Ballots, v \in Values : <<s, b, v>> \in proposed)
      ~> (\A l \in Learners : learned[l][s] # None)

LivenessGoal == (FairSpec /\ StableLeader) => Progress

=============================================================================
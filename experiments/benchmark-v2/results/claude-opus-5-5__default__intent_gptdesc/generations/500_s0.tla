------------------------------- MODULE MultiPaxos -------------------------------
(***************************************************************************)
(* Multi-decree Paxos (Multi-Paxos) with distinct proposers, acceptors     *)
(* and learners communicating by message passing.  A proposer acquires a   *)
(* ballot with one aggregated prepare (phase 1) that covers every slot,    *)
(* and then proposes values for individual slots in that ballot           *)
(* (phase 2).  Messages are never removed from the network, so they can   *)
(* be delayed, reordered or duplicated.  Message loss is modeled by the   *)
(* receiver never acting on a message.                                    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Proposers,     \* finite set of proposers
          Acceptors,     \* finite set of acceptors
          Learners,      \* finite set of learners
          Quorums,       \* set of quorums (subsets of Acceptors)
          Slots,         \* finite set of ordered log slots
          Ballots,       \* finite set of ballot numbers (naturals)
          Values,        \* finite set of proposable values
          BallotOwner,   \* each ballot belongs to exactly one proposer
          Leader,        \* the eventually-stable, correct leader
          LiveQuorum     \* a quorum of correct, eventually responsive acceptors

None == CHOOSE v : v \notin Values

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ Quorums # {}
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}   \* valid quorum intersection

ASSUME BallotAssumption ==
          /\ Ballots \subseteq Nat
          /\ Ballots # {}
          /\ BallotOwner \in [Ballots -> Proposers]

ASSUME FiniteAssumption ==
          /\ IsFiniteSet(Proposers) /\ IsFiniteSet(Acceptors)
          /\ IsFiniteSet(Learners)  /\ IsFiniteSet(Slots)
          /\ IsFiniteSet(Ballots)   /\ IsFiniteSet(Values)

MaxBallot == CHOOSE b \in Ballots : \A c \in Ballots : c <= b

(* Liveness assumptions: a single stable correct leader that owns the      *)
(* highest ballot, and a quorum of acceptors that keeps responding.         *)
ASSUME LivenessAssumption ==
          /\ Leader \in Proposers
          /\ BallotOwner[MaxBallot] = Leader
          /\ LiveQuorum \in Quorums

NoBallot == -1
BallotOrNone == Ballots \cup {NoBallot}

Vote == [bal : BallotOrNone, val : Values \cup {None}]
NoVote == [bal |-> NoBallot, val |-> None]

Messages ==
       [type : {"1a"}, bal : Ballots, from : Proposers]
  \cup [type : {"1b"}, bal : Ballots, acc : Acceptors, votes : [Slots -> Vote]]
  \cup [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, bal : Ballots, slot : Slots, val : Values, acc : Acceptors]

VARIABLES msgs,       \* the set of all messages ever sent
          maxBal,     \* maxBal[a]: highest ballot acceptor a has promised
          accepted,   \* accepted[a][s]: highest (ballot, value) a accepted for slot s
          pBallot,    \* pBallot[p]: current ballot of proposer p
          pPhase,     \* pPhase[p]: "idle", "p1" (preparing) or "p2" (leading)
          pQuorum,    \* pQuorum[p]: quorum whose promises p used in phase 1
          learned     \* learned[l][s]: value learner l learned for slot s

vars == <<msgs, maxBal, accepted, pBallot, pPhase, pQuorum, learned>>

TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxBal \in [Acceptors -> BallotOrNone]
  /\ accepted \in [Acceptors -> [Slots -> Vote]]
  /\ pBallot \in [Proposers -> BallotOrNone]
  /\ pPhase \in [Proposers -> {"idle", "p1", "p2"}]
  /\ pQuorum \in [Proposers -> SUBSET Acceptors]
  /\ learned \in [Learners -> [Slots -> Values \cup {None}]]

Init ==
  /\ msgs = {}
  /\ maxBal = [a \in Acceptors |-> NoBallot]
  /\ accepted = [a \in Acceptors |-> [s \in Slots |-> NoVote]]
  /\ pBallot = [p \in Proposers |-> NoBallot]
  /\ pPhase = [p \in Proposers |-> "idle"]
  /\ pQuorum = [p \in Proposers |-> {}]
  /\ learned = [l \in Learners |-> [s \in Slots |-> None]]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* Proposer actions *)

(* Proposer p picks a new, higher ballot that it owns.  It sends a single  *)
(* aggregated prepare covering all slots.                                   *)
Prepare(p, b) ==
  /\ BallotOwner[b] = p
  /\ b > pBallot[p]
  /\ pBallot' = [pBallot EXCEPT ![p] = b]
  /\ pPhase' = [pPhase EXCEPT ![p] = "p1"]
  /\ pQuorum' = [pQuorum EXCEPT ![p] = {}]
  /\ Send([type |-> "1a", bal |-> b, from |-> p])
  /\ UNCHANGED <<maxBal, accepted, learned>>

(* Proposer p has collected promises from a whole quorum Q for its ballot. *)
StartPhase2(p, Q) ==
  /\ pPhase[p] = "p1"
  /\ \A a \in Q : \E m \in msgs : /\ m.type = "1b"
                                  /\ m.bal = pBallot[p]
                                  /\ m.acc = a
  /\ pPhase' = [pPhase EXCEPT ![p] = "p2"]
  /\ pQuorum' = [pQuorum EXCEPT ![p] = Q]
  /\ UNCHANGED <<msgs, maxBal, accepted, pBallot, learned>>

(* Values p may safely propose for slot s.  If any acceptor in the         *)
(* promising quorum has accepted a value for s, p must use the value with  *)
(* the highest ballot.  Otherwise p may use any value.                      *)
SafeValues(p, s) ==
  LET Q1b   == {m \in msgs : /\ m.type = "1b"
                             /\ m.bal = pBallot[p]
                             /\ m.acc \in pQuorum[p]}
      Voted == {m \in Q1b : m.votes[s].bal # NoBallot}
      Top   == {m \in Voted : \A m2 \in Voted : m2.votes[s].bal <= m.votes[s].bal}
  IN  IF Voted = {} THEN Values ELSE {m.votes[s].val : m \in Top}

(* Proposer p proposes value v for slot s in its current ballot.  It       *)
(* makes at most one proposal per slot per ballot.                          *)
Propose(p, s, v) ==
  /\ pPhase[p] = "p2"
  /\ ~ \E m \in msgs : /\ m.type = "2a"
                       /\ m.bal = pBallot[p]
                       /\ m.slot = s
  /\ v \in SafeValues(p, s)
  /\ Send([type |-> "2a", bal |-> pBallot[p], slot |-> s, val |-> v])
  /\ UNCHANGED <<maxBal, accepted, pBallot, pPhase, pQuorum, learned>>

-----------------------------------------------------------------------------
(* Acceptor actions *)

(* Acceptor a promises a strictly higher ballot.  It replies with its      *)
(* accepted (ballot, value) for every slot.  Prepares with a lower ballot  *)
(* are refused, because this action is not enabled for them.                *)
Promise(a, m) ==
  /\ m.type = "1a"
  /\ m.bal > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
  /\ Send([type |-> "1b", bal |-> m.bal, acc |-> a, votes |-> accepted[a]])
  /\ UNCHANGED <<accepted, pBallot, pPhase, pQuorum, learned>>

(* Acceptor a accepts a proposal whose ballot is not lower than its        *)
(* promise.  Proposals with a lower ballot are refused.                     *)
Accept(a, m) ==
  /\ m.type = "2a"
  /\ m.bal >= maxBal[a]
  /\ ~ \E m2 \in msgs : /\ m2.type = "2b"
                        /\ m2.acc = a
                        /\ m2.bal = m.bal
                        /\ m2.slot = m.slot
  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
  /\ accepted' = [accepted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
  /\ Send([type |-> "2b", bal |-> m.bal, slot |-> m.slot,
           val |-> m.val, acc |-> a])
  /\ UNCHANGED <<pBallot, pPhase, pQuorum, learned>>

-----------------------------------------------------------------------------
(* Learner actions *)

(* Value v for slot s is chosen in ballot b if every acceptor of some      *)
(* quorum has accepted (b, v) for s.                                        *)
ChosenAt(s, b, v) ==
  \E Q \in Quorums : \A a \in Q :
     \E m \in msgs : /\ m.type = "2b"
                     /\ m.acc = a
                     /\ m.bal = b
                     /\ m.slot = s
                     /\ m.val = v

Chosen(s, v) == \E b \in Ballots : ChosenAt(s, b, v)

(* Learner l observes matching acceptances from a whole quorum. *)
Learn(l, s, v) ==
  /\ learned[l][s] = None
  /\ Chosen(s, v)
  /\ learned' = [learned EXCEPT ![l][s] = v]
  /\ UNCHANGED <<msgs, maxBal, accepted, pBallot, pPhase, pQuorum>>

-----------------------------------------------------------------------------
Next ==
  \/ \E p \in Proposers, b \in Ballots : Prepare(p, b)
  \/ \E p \in Proposers, Q \in Quorums : StartPhase2(p, Q)
  \/ \E p \in Proposers, s \in Slots, v \in Values : Propose(p, s, v)
  \/ \E a \in Acceptors, m \in msgs : Promise(a, m)
  \/ \E a \in Acceptors, m \in msgs : Accept(a, m)
  \/ \E l \in Learners, s \in Slots, v \in Values : Learn(l, s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Fairness: a stable correct leader, eventual reliable communication     *)
(* with a responsive quorum of acceptors, and learners that keep acting.  *)

LeaderFairness ==
  /\ WF_vars(\E b \in Ballots : Prepare(Leader, b))
  /\ WF_vars(\E Q \in Quorums : StartPhase2(Leader, Q))
  /\ \A s \in Slots : WF_vars(\E v \in Values : Propose(Leader, s, v))

AcceptorFairness ==
  \A a \in LiveQuorum :
     /\ WF_vars(\E m \in msgs : Promise(a, m))
     /\ WF_vars(\E m \in msgs : Accept(a, m))

LearnerFairness ==
  \A l \in Learners, s \in Slots : WF_vars(\E v \in Values : Learn(l, s, v))

LiveSpec == Spec /\ LeaderFairness /\ AcceptorFairness /\ LearnerFairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* (1) Agreement: at most one value is ever chosen for each slot. *)
Agreement ==
  \A s \in Slots, v1, v2 \in Values :
     (Chosen(s, v1) /\ Chosen(s, v2)) => (v1 = v2)

(* Learners never disagree, and they learn only chosen values. *)
LearnerConsistency ==
  \A l1, l2 \in Learners, s \in Slots :
     (learned[l1][s] # None /\ learned[l2][s] # None)
        => learned[l1][s] = learned[l2][s]

LearnedIsChosen ==
  \A l \in Learners, s \in Slots :
     learned[l][s] # None => Chosen(s, learned[l][s])

(* (2) Integrity: a chosen value was proposed by some proposer. *)
Integrity ==
  \A s \in Slots, v \in Values :
     Chosen(s, v) =>
        \E m \in msgs : /\ m.type = "2a"
                        /\ m.slot = s
                        /\ m.val = v
                        /\ BallotOwner[m.bal] \in Proposers

(* An acceptor never accepts in a ballot above its promise. *)
AcceptedBelowPromise ==
  \A a \in Acceptors, s \in Slots : accepted[a][s].bal <= maxBal[a]

(* There is at most one proposal per (ballot, slot). *)
UniqueProposal ==
  \A m1, m2 \in msgs :
     (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal /\ m1.slot = m2.slot)
        => m1.val = m2.val

SafetyInvariant ==
  /\ TypeOK
  /\ Agreement
  /\ LearnerConsistency
  /\ LearnedIsChosen
  /\ Integrity
  /\ AcceptedBelowPromise
  /\ UniqueProposal

(* (3) Monotonic ballots: promised ballots never decrease. *)
MonotonicBallots ==
  [][\A a \in Acceptors : maxBal'[a] >= maxBal[a]]_vars

MonotonicProposerBallots ==
  [][\A p \in Proposers : pBallot'[p] >= pBallot[p]]_vars

(* Learned values are never retracted. *)
StableLearning ==
  [][\A l \in Learners, s \in Slots :
        learned[l][s] # None => learned'[l][s] = learned[l][s]]_vars

(* (4) Valid quorum intersection, assumed as a system parameter. *)
QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

THEOREM QuorumIntersectionHolds == QuorumIntersection
  BY QuorumAssumption

-----------------------------------------------------------------------------
(* Liveness properties, which hold under LiveSpec *)

(* Progress: every slot is eventually decided and learned by every learner. *)
Progress ==
  \A s \in Slots : <>(\A l \in Learners : learned[l][s] # None)

(* Every slot eventually has a chosen value. *)
EventuallyChosen ==
  \A s \in Slots : <>(\E v \in Values : Chosen(s, v))

(* Once a value is proposed for a slot, some value is eventually learned *)
(* for that slot by every learner.                                        *)
ProposedEventuallyLearned ==
  \A s \in Slots :
     (\E m \in msgs : m.type = "2a" /\ m.slot = s)
        ~> (\A l \in Learners : learned[l][s] # None)

THEOREM SafetyTheorem ==
  Spec => /\ []SafetyInvariant
          /\ MonotonicBallots
          /\ MonotonicProposerBallots
          /\ StableLearning

THEOREM LivenessTheorem ==
  LiveSpec => /\ Progress
              /\ EventuallyChosen
              /\ ProposedEventuallyLearned
=============================================================================
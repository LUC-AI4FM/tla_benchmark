------------------------------ MODULE MultiPaxosRSM ------------------------------
(***************************************************************************)
(* Multi-decree Paxos replicated state machine.                            *)
(*                                                                         *)
(* Every replica plays proposer, acceptor and learner.                     *)
(* - Consensus runs independently in each slot of Slots. Slots may be Nat  *)
(*   to model an unbounded log; use a finite set for model checking.       *)
(* - Phase 1 is aggregated. One Prepare for ballot b covers every slot.    *)
(*   Each PrepareReply carries the acceptor's latest vote for every slot.  *)
(* - Phase 2 (Accept / AcceptReply) runs per slot.                         *)
(* - Messages accumulate in a buffer and are received nondeterministically.*)
(*   Every message may be delayed forever, which models loss. A message    *)
(*   may also be received many times, which models duplication. Nothing    *)
(*   assumes synchrony.                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Replicas,   \* finite set of replicas (proposer/acceptor/learner)
          Ballots,    \* finite set of ballot numbers, a subset of Nat
          Values,     \* finite set of proposable values (commands)
          Slots,      \* set of log slots (consensus instances)
          Owner       \* Owner[b] is the unique replica allowed to lead ballot b

ASSUME /\ Replicas # {}
       /\ IsFiniteSet(Replicas)
       /\ Ballots \subseteq Nat
       /\ Values # {}
       /\ Owner \in [Ballots -> Replicas]

None == CHOOSE x : x \notin Values

NoBallot == -1

(* Majority quorums *)
Quorums == { Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas) }

(* Majority quorums pairwise intersect. *)
QuorumAssumption == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

THEOREM QuorumIntersection == QuorumAssumption

VARIABLES
  msgs,       \* set of all messages ever sent (the asynchronous network buffer)
  leaderBal,  \* leaderBal[r]: highest ballot replica r has tried to lead
  isLeader,   \* isLeader[r]: r finished (aggregated) phase 1 for leaderBal[r]
  safeVal,    \* safeVal[r][s]: value r must propose in s (None means any value)
  proposed,   \* proposed[r][s]: value r proposed in s at leaderBal[r] (or None)
  promised,   \* promised[a]: highest ballot acceptor a has promised
  vBal,       \* vBal[a][s]: ballot of a's latest vote in slot s
  vVal,       \* vVal[a][s]: value of a's latest vote in slot s
  learned     \* learned[r][s]: value r has learned as decided for s (or None)

vars == << msgs, leaderBal, isLeader, safeVal, proposed,
           promised, vBal, vVal, learned >>

BallotOrNone == Ballots \cup {NoBallot}

ValOrNone == Values \cup {None}

Vote == [slot : Slots, bal : Ballots, val : Values]

Message ==
       [type : {"prepare"}, bal : Ballots, from : Replicas]
  \cup [type : {"prepareReply"}, bal : Ballots, from : Replicas,
        to : Replicas, votes : SUBSET Vote]
  \cup [type : {"accept"}, bal : Ballots, slot : Slots, val : Values,
        from : Replicas]
  \cup [type : {"acceptReply"}, bal : Ballots, slot : Slots, val : Values,
        from : Replicas]
  \cup [type : {"decide"}, slot : Slots, val : Values, from : Replicas]

TypeOK ==
  /\ msgs \subseteq Message
  /\ leaderBal \in [Replicas -> BallotOrNone]
  /\ isLeader \in [Replicas -> BOOLEAN]
  /\ safeVal \in [Replicas -> [Slots -> ValOrNone]]
  /\ proposed \in [Replicas -> [Slots -> ValOrNone]]
  /\ promised \in [Replicas -> BallotOrNone]
  /\ vBal \in [Replicas -> [Slots -> BallotOrNone]]
  /\ vVal \in [Replicas -> [Slots -> ValOrNone]]
  /\ learned \in [Replicas -> [Slots -> ValOrNone]]

Send(m) == msgs' = msgs \cup {m}

(* Helpers for choosing a value from prior votes *)
VotesForSlot(V, s) == { x \in V : x.slot = s }

(* The value of the highest-ballot vote for slot s in V, or None if no vote exists. *)
HighestVoteVal(V, s) ==
  IF VotesForSlot(V, s) = {}
  THEN None
  ELSE (CHOOSE x \in VotesForSlot(V, s) :
          \A y \in VotesForSlot(V, s) : y.bal <= x.bal).val

PrepareReplies(b, Q) ==
  { m \in msgs : m.type = "prepareReply" /\ m.bal = b /\ m.from \in Q }

-----------------------------------------------------------------------------
Init ==
  /\ msgs = {}
  /\ leaderBal = [r \in Replicas |-> NoBallot]
  /\ isLeader = [r \in Replicas |-> FALSE]
  /\ safeVal = [r \in Replicas |-> [s \in Slots |-> None]]
  /\ proposed = [r \in Replicas |-> [s \in Slots |-> None]]
  /\ promised = [a \in Replicas |-> NoBallot]
  /\ vBal = [a \in Replicas |-> [s \in Slots |-> NoBallot]]
  /\ vVal = [a \in Replicas |-> [s \in Slots |-> None]]
  /\ learned = [r \in Replicas |-> [s \in Slots |-> None]]

(* Phase 1a: r starts a new ballot it owns. The Prepare covers all slots. *)
Prepare(r, b) ==
  /\ Owner[b] = r
  /\ b > leaderBal[r]
  /\ leaderBal' = [leaderBal EXCEPT ![r] = b]
  /\ isLeader' = [isLeader EXCEPT ![r] = FALSE]
  /\ proposed' = [proposed EXCEPT ![r] = [s \in Slots |-> None]]
  /\ Send([type |-> "prepare", bal |-> b, from |-> r])
  /\ UNCHANGED << safeVal, promised, vBal, vVal, learned >>

(* Phase 1b: acceptor a promises ballot m.bal and reports its votes for all slots. *)
PrepareReply(a, m) ==
  /\ m \in msgs
  /\ m.type = "prepare"
  /\ m.bal > promised[a]
  /\ promised' = [promised EXCEPT ![a] = m.bal]
  /\ Send([type  |-> "prepareReply",
           bal   |-> m.bal,
           from  |-> a,
           to    |-> m.from,
           votes |-> { [slot |-> s, bal |-> vBal[a][s], val |-> vVal[a][s]] :
                         s \in { t \in Slots : vBal[a][t] # NoBallot } }])
  /\ UNCHANGED << leaderBal, isLeader, safeVal, proposed, vBal, vVal, learned >>

(* r collects PrepareReplies from a majority for its current ballot.
   For each slot it fixes the safe value: the value of the highest prior
   vote, or None (any value is allowed) if no prior vote exists. *)
BecomeLeader(r, Q) ==
  /\ leaderBal[r] # NoBallot
  /\ ~isLeader[r]
  /\ Q \in Quorums
  /\ \A a \in Q : \E m \in msgs : /\ m.type = "prepareReply"
                                  /\ m.bal = leaderBal[r]
                                  /\ m.from = a
                                  /\ m.to = r
  /\ LET V == UNION { m.votes : m \in PrepareReplies(leaderBal[r], Q) }
     IN  safeVal' = [safeVal EXCEPT ![r] = [s \in Slots |-> HighestVoteVal(V, s)]]
  /\ isLeader' = [isLeader EXCEPT ![r] = TRUE]
  /\ UNCHANGED << msgs, leaderBal, proposed, promised, vBal, vVal, learned >>

(* Phase 2a: leader r proposes a safe value v for slot s, at most once per ballot. *)
Propose(r, s, v) ==
  /\ isLeader[r]
  /\ proposed[r][s] = None
  /\ safeVal[r][s] \in {None, v}
  /\ proposed' = [proposed EXCEPT ![r][s] = v]
  /\ Send([type |-> "accept", bal |-> leaderBal[r], slot |-> s, val |-> v, from |-> r])
  /\ UNCHANGED << leaderBal, isLeader, safeVal, promised, vBal, vVal, learned >>

(* Phase 2b: acceptor a votes for the Accept unless it promised a higher ballot. *)
Accept(a, m) ==
  /\ m \in msgs
  /\ m.type = "accept"
  /\ m.bal >= promised[a]
  /\ promised' = [promised EXCEPT ![a] = m.bal]
  /\ vBal' = [vBal EXCEPT ![a][m.slot] = m.bal]
  /\ vVal' = [vVal EXCEPT ![a][m.slot] = m.val]
  /\ Send([type |-> "acceptReply", bal |-> m.bal, slot |-> m.slot,
           val |-> m.val, from |-> a])
  /\ UNCHANGED << leaderBal, isLeader, safeVal, proposed, learned >>

(* Learn: r sees AcceptReplies from a majority for the same (slot, ballot, value). *)
Learn(r, s, b, v, Q) ==
  /\ Q \in Quorums
  /\ \A a \in Q : [type |-> "acceptReply", bal |-> b, slot |-> s,
                   val |-> v, from |-> a] \in msgs
  /\ learned' = [learned EXCEPT ![r][s] = v]
  /\ Send([type |-> "decide", slot |-> s, val |-> v, from |-> r])
  /\ UNCHANGED << leaderBal, isLeader, safeVal, proposed, promised, vBal, vVal >>

(* A replica learns a decision announced by another replica. *)
ReceiveDecide(r, m) ==
  /\ m \in msgs
  /\ m.type = "decide"
  /\ learned' = [learned EXCEPT ![r][m.slot] = m.val]
  /\ UNCHANGED << msgs, leaderBal, isLeader, safeVal, proposed,
                  promised, vBal, vVal >>

Next ==
  \/ \E r \in Replicas, b \in Ballots : Prepare(r, b)
  \/ \E a \in Replicas, m \in msgs : PrepareReply(a, m)
  \/ \E r \in Replicas, Q \in Quorums : BecomeLeader(r, Q)
  \/ \E r \in Replicas, s \in Slots, v \in Values : Propose(r, s, v)
  \/ \E a \in Replicas, m \in msgs : Accept(a, m)
  \/ \E r \in Replicas, s \in Slots, b \in Ballots, v \in Values, Q \in Quorums :
        Learn(r, s, b, v, Q)
  \/ \E r \in Replicas, m \in msgs : ReceiveDecide(r, m)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Chosen: a majority of acceptors voted for v in slot s at the same ballot. *)
ChosenAt(s, b, v) ==
  \E Q \in Quorums : \A a \in Q :
     [type |-> "acceptReply", bal |-> b, slot |-> s, val |-> v, from |-> a] \in msgs

Chosen(s, v) == \E b \in Ballots : ChosenAt(s, b, v)

(* Safety (1) Agreement: at most one value is chosen per slot. *)
Agreement ==
  \A s \in Slots, v1, v2 \in Values :
     (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2

(* Safety (2) Integrity: every chosen value was proposed by some replica. *)
Integrity ==
  \A s \in Slots, v \in Values :
     Chosen(s, v) =>
        \E m \in msgs : /\ m.type = "accept"
                        /\ m.slot = s
                        /\ m.val = v
                        /\ m.from \in Replicas

(* Deciding requires a majority. Every learned or decided value is chosen. *)
DecisionRequiresQuorum ==
  /\ \A r \in Replicas, s \in Slots :
        learned[r][s] # None => Chosen(s, learned[r][s])
  /\ \A m \in msgs : m.type = "decide" => Chosen(m.slot, m.val)

(* No two replicas learn different values for the same slot. *)
LearnerConsistency ==
  \A r1, r2 \in Replicas, s \in Slots :
     (learned[r1][s] # None /\ learned[r2][s] # None) =>
        learned[r1][s] = learned[r2][s]

(* Quorum-justified proposals: every Accept is backed by PrepareReplies
   from a majority. The proposed value equals the highest prior vote
   reported for that slot, or any value if no prior vote was reported. *)
ProposalJustified ==
  \A m \in msgs :
     m.type = "accept" =>
        \E Q \in Quorums :
           /\ \A a \in Q : \E p \in msgs : /\ p.type = "prepareReply"
                                           /\ p.bal = m.bal
                                           /\ p.from = a
           /\ LET V == UNION { p.votes : p \in PrepareReplies(m.bal, Q) }
              IN  HighestVoteVal(V, m.slot) \in {None, m.val}

(* Each slot receives at most one proposal per ballot. *)
OneValuePerBallot ==
  \A m1, m2 \in msgs :
     (m1.type = "accept" /\ m2.type = "accept" /\
      m1.bal = m2.bal /\ m1.slot = m2.slot) => m1.val = m2.val

(* Only the ballot owner proposes in a ballot. *)
OwnerProposes ==
  \A m \in msgs : m.type = "accept" => Owner[m.bal] = m.from

(* An acceptor's votes never exceed its promise. *)
VoteBelowPromise ==
  \A a \in Replicas, s \in Slots : vBal[a][s] <= promised[a]

(* Votes recorded locally match a sent AcceptReply. *)
VotesAreSent ==
  \A a \in Replicas, s \in Slots :
     vBal[a][s] # NoBallot =>
        [type |-> "acceptReply", bal |-> vBal[a][s], slot |-> s,
         val |-> vVal[a][s], from |-> a] \in msgs

Inv ==
  /\ TypeOK
  /\ Agreement
  /\ Integrity
  /\ DecisionRequiresQuorum
  /\ LearnerConsistency
  /\ ProposalJustified
  /\ OneValuePerBallot
  /\ OwnerProposes
  /\ VoteBelowPromise
  /\ VotesAreSent

(* Ballot monotonicity: promises and leader ballots never decrease. *)
PromiseMonotonic ==
  [][\A a \in Replicas : promised'[a] >= promised[a]]_vars

LeaderBallotMonotonic ==
  [][\A r \in Replicas : leaderBal'[r] >= leaderBal[r]]_vars

(* Per-slot vote ballots never decrease. *)
VoteBallotMonotonic ==
  [][\A a \in Replicas, s \in Slots : vBal'[a][s] >= vBal[a][s]]_vars

(* The set of messages only grows. *)
MsgsMonotonic == [][msgs \subseteq msgs']_vars

THEOREM Spec => []Inv
THEOREM Spec => PromiseMonotonic /\ LeaderBallotMonotonic /\ VoteBallotMonotonic
=============================================================================
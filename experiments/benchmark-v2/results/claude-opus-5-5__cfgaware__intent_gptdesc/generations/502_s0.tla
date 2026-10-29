---------------------------- MODULE MultiPaxosRSM ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Replicas,   \* finite set of replicas (proposer + acceptor + learner)
          Ballots,    \* finite set of ballot numbers (naturals)
          Slots,      \* set of slots (consensus instances), finite in a model
          Values      \* set of possible command values

ASSUME BallotsAreNat == Ballots \subseteq Nat
ASSUME NonEmpty == Replicas # {} /\ Values # {}

VARIABLES
  lBallot,   \* lBallot[r] : ballot currently used by r as leader (-1 = none)
  lStatus,   \* lStatus[r] : "idle", "preparing" or "leading"
  proposed,  \* proposed[r][s] : {} or {v}, value r proposed for s in lBallot[r]
  learned,   \* learned[r][s]  : {} or {v}, value r has learned for slot s
  rBallot,   \* rBallot[r] : highest ballot r (as acceptor) has promised
  rVoted,    \* rVoted[r][s] : [bal, val] last vote of acceptor r in slot s
  msgs       \* set of all messages ever sent (buffered, unordered, lossy)

vars == <<lBallot, lStatus, proposed, learned, rBallot, rVoted, msgs>>

-----------------------------------------------------------------------------
DefaultVal == CHOOSE v \in Values : TRUE
NoVote     == [bal |-> -1, val |-> DefaultVal]

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

Vote == [bal : Ballots \cup {-1}, val : Values]

Messages ==
       [type : {"Prepare"}, from : Replicas, bal : Ballots]
  \cup [type : {"PrepareReply"}, from : Replicas, to : Replicas,
        bal : Ballots, votes : [Slots -> Vote]]
  \cup [type : {"Accept"}, from : Replicas, bal : Ballots,
        slot : Slots, val : Values]
  \cup [type : {"AcceptReply"}, from : Replicas, to : Replicas,
        bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"Decide"}, from : Replicas, slot : Slots, val : Values]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
TypeOK ==
  /\ lBallot  \in [Replicas -> Ballots \cup {-1}]
  /\ lStatus  \in [Replicas -> {"idle", "preparing", "leading"}]
  /\ proposed \in [Replicas -> [Slots -> SUBSET Values]]
  /\ learned  \in [Replicas -> [Slots -> SUBSET Values]]
  /\ rBallot  \in [Replicas -> Ballots \cup {-1}]
  /\ rVoted   \in [Replicas -> [Slots -> Vote]]
  /\ msgs     \subseteq Messages

Init ==
  /\ lBallot  = [r \in Replicas |-> -1]
  /\ lStatus  = [r \in Replicas |-> "idle"]
  /\ proposed = [r \in Replicas |-> [s \in Slots |-> {}]]
  /\ learned  = [r \in Replicas |-> [s \in Slots |-> {}]]
  /\ rBallot  = [r \in Replicas |-> -1]
  /\ rVoted   = [r \in Replicas |-> [s \in Slots |-> NoVote]]
  /\ msgs     = {}

-----------------------------------------------------------------------------
(* Phase 1a: r starts a new ballot b.  One Prepare covers ALL slots.        *)
(* Ballots are unique per proposer: no other replica has prepared b.       *)
Prepare(r, b) ==
  /\ b > lBallot[r]
  /\ \A m \in msgs : m.type = "Prepare" => m.bal # b
  /\ lBallot'  = [lBallot EXCEPT ![r] = b]
  /\ lStatus'  = [lStatus EXCEPT ![r] = "preparing"]
  /\ proposed' = [proposed EXCEPT ![r] = [s \in Slots |-> {}]]
  /\ Send([type |-> "Prepare", from |-> r, bal |-> b])
  /\ UNCHANGED <<learned, rBallot, rVoted>>

(* Phase 1b: acceptor a promises ballot m.bal and reports votes of all slots *)
HandlePrepare(a, m) ==
  /\ m \in msgs
  /\ m.type = "Prepare"
  /\ m.bal > rBallot[a]
  /\ rBallot' = [rBallot EXCEPT ![a] = m.bal]
  /\ Send([type |-> "PrepareReply", from |-> a, to |-> m.from,
           bal |-> m.bal, votes |-> rVoted[a]])
  /\ UNCHANGED <<lBallot, lStatus, proposed, learned, rVoted>>

PrepareReplies(r, Q) ==
  {m \in msgs : /\ m.type = "PrepareReply"
                /\ m.to = r
                /\ m.bal = lBallot[r]
                /\ m.from \in Q}

HasPrepareQuorum(r, Q) ==
  \A q \in Q : \E m \in PrepareReplies(r, Q) : m.from = q

(* v is safe for slot s w.r.t. the replies of quorum Q: either no acceptor  *)
(* in Q voted in s, or v is the value of the highest-ballot vote.          *)
SafeValue(r, s, v, Q) ==
  LET votes == {m.votes[s] : m \in PrepareReplies(r, Q)}
  IN  \/ \A vt \in votes : vt.bal = -1
      \/ \E vt \in votes : /\ vt.bal # -1
                           /\ vt.val = v
                           /\ \A w \in votes : w.bal <= vt.bal

(* r becomes leader for all slots once a majority promised its ballot *)
BecomeLeader(r, Q) ==
  /\ lStatus[r] = "preparing"
  /\ Q \in Quorums
  /\ HasPrepareQuorum(r, Q)
  /\ lStatus' = [lStatus EXCEPT ![r] = "leading"]
  /\ UNCHANGED <<lBallot, proposed, learned, rBallot, rVoted, msgs>>

(* Phase 2a: propose a safe value for slot s (at most once per ballot) *)
Propose(r, s, v, Q) ==
  /\ lStatus[r] = "leading"
  /\ proposed[r][s] = {}
  /\ Q \in Quorums
  /\ HasPrepareQuorum(r, Q)
  /\ SafeValue(r, s, v, Q)
  /\ proposed' = [proposed EXCEPT ![r][s] = {v}]
  /\ Send([type |-> "Accept", from |-> r, bal |-> lBallot[r],
           slot |-> s, val |-> v])
  /\ UNCHANGED <<lBallot, lStatus, learned, rBallot, rVoted>>

(* Phase 2b: acceptor a votes if it has not promised a higher ballot *)
HandleAccept(a, m) ==
  /\ m \in msgs
  /\ m.type = "Accept"
  /\ m.bal >= rBallot[a]
  /\ rBallot' = [rBallot EXCEPT ![a] = m.bal]
  /\ rVoted'  = [rVoted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
  /\ Send([type |-> "AcceptReply", from |-> a, to |-> m.from,
           bal |-> m.bal, slot |-> m.slot, val |-> m.val])
  /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

(* Learning: a majority of AcceptReplies for (b, s, v) decides s *)
Learn(r, s, b, v, Q) ==
  /\ learned[r][s] = {}
  /\ Q \in Quorums
  /\ \A q \in Q : \E m \in msgs : /\ m.type = "AcceptReply"
                                  /\ m.from = q
                                  /\ m.bal = b
                                  /\ m.slot = s
                                  /\ m.val = v
  /\ learned' = [learned EXCEPT ![r][s] = {v}]
  /\ Send([type |-> "Decide", from |-> r, slot |-> s, val |-> v])
  /\ UNCHANGED <<lBallot, lStatus, proposed, rBallot, rVoted>>

(* Learning from another replica's decision *)
HandleDecide(r, m) ==
  /\ m \in msgs
  /\ m.type = "Decide"
  /\ learned[r][m.slot] = {}
  /\ learned' = [learned EXCEPT ![r][m.slot] = {m.val}]
  /\ UNCHANGED <<lBallot, lStatus, proposed, rBallot, rVoted, msgs>>

Next ==
  \/ \E r \in Replicas, b \in Ballots : Prepare(r, b)
  \/ \E r \in Replicas, m \in msgs : HandlePrepare(r, m)
  \/ \E r \in Replicas, Q \in Quorums : BecomeLeader(r, Q)
  \/ \E r \in Replicas, s \in Slots, v \in Values, Q \in Quorums :
        Propose(r, s, v, Q)
  \/ \E r \in Replicas, m \in msgs : HandleAccept(r, m)
  \/ \E r \in Replicas, s \in Slots, b \in Ballots, v \in Values,
        Q \in Quorums : Learn(r, s, b, v, Q)
  \/ \E r \in Replicas, m \in msgs : HandleDecide(r, m)

(* Messages are never required to be delivered: loss, delay, duplication  *)
(* and reordering are all modeled by the set-based buffer msgs.            *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

Chosen(s, v) ==
  \E b \in Ballots, Q \in Quorums :
    \A q \in Q : \E m \in msgs : /\ m.type = "AcceptReply"
                                 /\ m.from = q
                                 /\ m.bal = b
                                 /\ m.slot = s
                                 /\ m.val = v

Agreement ==
  \A s \in Slots, v1, v2 \in Values :
    (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2

Integrity ==
  \A s \in Slots, v \in Values :
    Chosen(s, v) => \E m \in msgs : /\ m.type = "Accept"
                                    /\ m.slot = s
                                    /\ m.val = v

LearnedChosen ==
  \A r \in Replicas, s \in Slots : \A v \in learned[r][s] : Chosen(s, v)

LearnedAgreement ==
  \A r1, r2 \in Replicas, s \in Slots :
    (learned[r1][s] # {} /\ learned[r2][s] # {}) =>
       learned[r1][s] = learned[r2][s]

QuorumIntersection ==
  \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

(* Every Accept message was justified by a majority of PrepareReplies *)
AcceptJustified ==
  \A m \in msgs : m.type = "Accept" =>
     \E Q \in Quorums :
        \A q \in Q : \E p \in msgs : /\ p.type = "PrepareReply"
                                     /\ p.from = q
                                     /\ p.to = m.from
                                     /\ p.bal = m.bal

(* Acceptors never vote above their promise *)
VoteBelowPromise ==
  \A a \in Replicas, s \in Slots : rVoted[a][s].bal <= rBallot[a]

Inv ==
  /\ TypeOK
  /\ Agreement
  /\ Integrity
  /\ LearnedChosen
  /\ LearnedAgreement
  /\ QuorumIntersection
  /\ AcceptJustified
  /\ VoteBelowPromise

(* Ballot monotonicity: promises and leader ballots never decrease *)
PromiseMonotonic ==
  [][\A a \in Replicas : rBallot'[a] >= rBallot[a]]_vars

LeaderBallotMonotonic ==
  [][\A r \in Replicas : lBallot'[r] >= lBallot[r]]_vars

LearnedStable ==
  [][\A r \in Replicas, s \in Slots :
        learned[r][s] # {} => learned'[r][s] = learned[r][s]]_vars

THEOREM Spec => []Inv
=============================================================================
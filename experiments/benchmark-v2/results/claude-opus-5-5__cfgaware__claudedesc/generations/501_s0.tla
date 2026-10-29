---------------------------- MODULE MultiPaxos ----------------------------
(***************************************************************************)
(* Multi-Paxos consensus over multiple slots, with model-checking          *)
(* definitions.                                                            *)
(*                                                                         *)
(* Replicas act both as leaders and as acceptors. A leader picks an unused *)
(* ballot and broadcasts Prepare. Once a quorum of PrepareReplies arrives  *)
(* for that ballot, it proposes a value per slot: the highest-ballot value *)
(* already voted in that quorum, or any value if none was voted. It then   *)
(* broadcasts Accept. Once a quorum of AcceptReplies arrives for a slot,   *)
(* the value is learned for that slot.                                     *)
(*                                                                         *)
(* Refinement of ConsensusMulti maps proposed |-> UNION of proposed[s]     *)
(* and learned |-> learned. Full temporal refinement checking should only  *)
(* run on very small inputs because of state explosion. The safety         *)
(* invariants NontrivialityInv and ConsistencyInv are checked directly.    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

VARIABLES msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned

vars == <<msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned>>

----------------------------------------------------------------------------
(* Model-checking helpers *)

ConstBallots == 0..1

SymmetricPerms == Permutations(Replicas)
                    \union Permutations(Values)
                    \union Permutations(Slots)

----------------------------------------------------------------------------
NullValue == CHOOSE v : v \notin Values

VoteType == [bal : Ballots \union {-1}, val : Values \union {NullValue}]

NullVote == [bal |-> -1, val |-> NullValue]

Statuses == {"", "Preparing", "Accepting", "Learned"}

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

PrepareMsgs ==
    [type : {"Prepare"}, src : Replicas, bal : Ballots]

PrepareReplyMsgs ==
    [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
     voted : [Slots -> VoteType]]

AcceptMsgs ==
    [type : {"Accept"}, src : Replicas, bal : Ballots,
     slot : Slots, val : Values]

AcceptReplyMsgs ==
    [type : {"AcceptReply"}, src : Replicas, bal : Ballots,
     slot : Slots, val : Values]

Messages == PrepareMsgs \union PrepareReplyMsgs
              \union AcceptMsgs \union AcceptReplyMsgs

TypeOK ==
    /\ msgs \subseteq Messages
    /\ lBallot \in [Replicas -> Ballots \union {-1}]
    /\ lStatus \in [Replicas -> [Slots -> Statuses]]
    /\ rBallot \in [Replicas -> Ballots \union {-1}]
    /\ rVoted \in [Replicas -> [Slots -> VoteType]]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Slots -> SUBSET Values]

Send(m) == msgs' = msgs \union {m}

----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ lBallot = [r \in Replicas |-> -1]
    /\ lStatus = [r \in Replicas |-> [s \in Slots |-> ""]]
    /\ rBallot = [r \in Replicas |-> -1]
    /\ rVoted = [r \in Replicas |-> [s \in Slots |-> NullVote]]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [s \in Slots |-> {}]

(* Leader r starts a new, globally unused ballot b. *)
PrepareBallot(r, b) ==
    /\ b > lBallot[r]
    /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ lBallot' = [lBallot EXCEPT ![r] = b]
    /\ lStatus' = [lStatus EXCEPT ![r] = [s \in Slots |-> "Preparing"]]
    /\ Send([type |-> "Prepare", src |-> r, bal |-> b])
    /\ UNCHANGED <<rBallot, rVoted, proposed, learned>>

(* Replica r promises a higher ballot and reports its votes. *)
HandlePrepare(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ Send([type |-> "PrepareReply", src |-> r, bal |-> m.bal,
                 voted |-> rVoted[r]])
        /\ UNCHANGED <<lBallot, lStatus, rVoted, proposed, learned>>

(* Leader r gets a quorum of promises and proposes a value for slot s. *)
ProposeAccept(r, s) ==
    /\ lBallot[r] # -1
    /\ lStatus[r][s] = "Preparing"
    /\ \E Q \in Quorums :
        LET b       == lBallot[r]
            replies == {m \in msgs : /\ m.type = "PrepareReply"
                                     /\ m.bal = b
                                     /\ m.src \in Q}
            prior   == {m.voted[s] : m \in replies} \ {NullVote}
            prior2  == {pv \in prior : pv.bal # -1}
        IN  /\ \A q \in Q : \E m \in replies : m.src = q
            /\ \E v \in Values :
                /\ IF prior2 = {}
                     THEN TRUE
                     ELSE v = (CHOOSE pv \in prior2 :
                                 \A o \in prior2 : o.bal <= pv.bal).val
                /\ Send([type |-> "Accept", src |-> r, bal |-> b,
                         slot |-> s, val |-> v])
                /\ proposed' = [proposed EXCEPT ![s] = @ \union {v}]
    /\ lStatus' = [lStatus EXCEPT ![r][s] = "Accepting"]
    /\ UNCHANGED <<lBallot, rBallot, rVoted, learned>>

(* Replica r votes for an Accept with ballot not below its promise. *)
HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= rBallot[r]
        /\ ~ \E m2 \in msgs : /\ m2.type = "AcceptReply"
                              /\ m2.src = r
                              /\ m2.bal = m.bal
                              /\ m2.slot = m.slot
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ rVoted' = [rVoted EXCEPT ![r][m.slot] =
                        [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "AcceptReply", src |-> r, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

(* Leader r gets a quorum of votes for slot s and learns the value. *)
LearnValue(r, s) ==
    /\ lBallot[r] # -1
    /\ lStatus[r][s] = "Accepting"
    /\ \E am \in msgs :
        /\ am.type = "Accept"
        /\ am.src = r
        /\ am.bal = lBallot[r]
        /\ am.slot = s
        /\ \E Q \in Quorums :
             \A q \in Q : \E m \in msgs :
                 /\ m.type = "AcceptReply"
                 /\ m.src = q
                 /\ m.bal = lBallot[r]
                 /\ m.slot = s
                 /\ m.val = am.val
        /\ learned' = [learned EXCEPT ![s] = @ \union {am.val}]
    /\ lStatus' = [lStatus EXCEPT ![r][s] = "Learned"]
    /\ UNCHANGED <<msgs, lBallot, rBallot, rVoted, proposed>>

Next ==
    \/ \E r \in Replicas, b \in Ballots : PrepareBallot(r, b)
    \/ \E r \in Replicas : HandlePrepare(r)
    \/ \E r \in Replicas, s \in Slots : ProposeAccept(r, s)
    \/ \E r \in Replicas : HandleAccept(r)
    \/ \E r \in Replicas, s \in Slots : LearnValue(r, s)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(* Safety invariants *)

NontrivialityInv ==
    \A s \in Slots : learned[s] \subseteq proposed[s]

ConsistencyInv ==
    \A s \in Slots : Cardinality(learned[s]) <= 1

(* Refinement mapping state for ConsensusMulti *)
AbsProposed == UNION {proposed[s] : s \in Slots}
AbsLearned  == learned

=============================================================================
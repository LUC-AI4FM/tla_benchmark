------------------------------ MODULE MC_MultiPaxos ------------------------------
(***************************************************************************)
(* Model-checking configuration for a Multi-Paxos consensus protocol.      *)
(* Three replicas, two values, two slots, and ballots 0..1.                *)
(*                                                                         *)
(* Checked directly: TypeOK, NontrivialityInv, ConsistencyInv.             *)
(* Checked as a temporal property: refinement of an inlined ConsensusMulti *)
(* abstract spec. Run full temporal refinement checking only on very small *)
(* inputs, because of state explosion.                                     *)
(*                                                                         *)
(* Symmetry is applied across replicas, values, and slots.                 *)
(* Deadlock checking is disabled in the TLC configuration                  *)
(* (CHECK_DEADLOCK FALSE).                                                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS r1, r2, r3,   \* model values for replicas
          v1, v2,       \* model values for values
          s1, s2        \* model values for slots

Replicas == {r1, r2, r3}
Values   == {v1, v2}
Slots    == {s1, s2}
Ballots  == 0..1

NullBal == -1
NullVal == "none"

ASSUME Cardinality(Replicas) = 3 /\ Cardinality(Values) = 2 /\ Cardinality(Slots) = 2

VARIABLES msgs,      \* set of protocol messages sent so far
          lBallot,   \* lBallot[r]: current ballot of r acting as leader
          lStatus,   \* lStatus[r][s]: leader per-slot status
          rBallot,   \* rBallot[r]: highest ballot seen by r acting as acceptor
          rVoted,    \* rVoted[r][s]: latest vote of r for slot s
          proposed,  \* proposed[s]: set of values proposed for slot s
          learned    \* learned[s]: set of values decided for slot s

vars == <<msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned>>

-----------------------------------------------------------------------------
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

StatusSet == {"Idle", "Preparing", "Accepting", "Learned"}

VotedType == [bal : Ballots \cup {NullBal}, val : Values \cup {NullVal}]
NullVote  == [bal |-> NullBal, val |-> NullVal]

PrepareMsgs      == [type : {"Prepare"}, src : Replicas, bal : Ballots]
PrepareReplyMsgs == [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
                     voted : [Slots -> VotedType]]
AcceptMsgs       == [type : {"Accept"}, src : Replicas, slot : Slots,
                     bal : Ballots, val : Values]
AcceptReplyMsgs  == [type : {"AcceptReply"}, src : Replicas, slot : Slots,
                     bal : Ballots]

Messages == PrepareMsgs \cup PrepareReplyMsgs \cup AcceptMsgs \cup AcceptReplyMsgs

TypeOK ==
    /\ msgs \subseteq Messages
    /\ lBallot \in [Replicas -> Ballots \cup {NullBal}]
    /\ lStatus \in [Replicas -> [Slots -> StatusSet]]
    /\ rBallot \in [Replicas -> Ballots \cup {NullBal}]
    /\ rVoted \in [Replicas -> [Slots -> VotedType]]
    /\ proposed \in [Slots -> SUBSET Values]
    /\ learned \in [Slots -> SUBSET Values]

Send(m) == msgs' = msgs \cup {m}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

-----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ lBallot = [r \in Replicas |-> NullBal]
    /\ lStatus = [r \in Replicas |-> [s \in Slots |-> "Idle"]]
    /\ rBallot = [r \in Replicas |-> NullBal]
    /\ rVoted = [r \in Replicas |-> [s \in Slots |-> NullVote]]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [s \in Slots |-> {}]

(* Leader r starts the prepare phase with a fresh, unused ballot b. *)
Prepare(r, b) ==
    /\ b > lBallot[r]
    /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ lBallot' = [lBallot EXCEPT ![r] = b]
    /\ lStatus' = [lStatus EXCEPT ![r] = [s \in Slots |-> "Preparing"]]
    /\ Send([type |-> "Prepare", src |-> r, bal |-> b])
    /\ UNCHANGED <<rBallot, rVoted, proposed, learned>>

(* Acceptor r handles a Prepare with a higher ballot. *)
HandlePrepare(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ Send([type |-> "PrepareReply", src |-> r, bal |-> m.bal,
                 voted |-> rVoted[r]])
        /\ UNCHANGED <<lBallot, lStatus, rVoted, proposed, learned>>

(* Leader r, after a quorum of PrepareReplies, proposes a safe value v *)
(* for slot s and sends an Accept.                                     *)
Accept(r, s, v) ==
    /\ lStatus[r][s] = "Preparing"
    /\ \E Q \in Quorums :
         LET replies == {m \in msgs : /\ m.type = "PrepareReply"
                                      /\ m.bal = lBallot[r]
                                      /\ m.src \in Q}
             votes   == {m.voted[s] : m \in replies}
             maxBal  == Max({vt.bal : vt \in votes})
         IN  /\ \A q \in Q : \E m \in replies : m.src = q
             /\ \/ maxBal = NullBal
                \/ \E vt \in votes : vt.bal = maxBal /\ vt.val = v
    /\ lStatus' = [lStatus EXCEPT ![r][s] = "Accepting"]
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ Send([type |-> "Accept", src |-> r, slot |-> s,
             bal |-> lBallot[r], val |-> v])
    /\ UNCHANGED <<lBallot, rBallot, rVoted, learned>>

(* Acceptor r handles an Accept with ballot >= its current ballot. *)
HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= rBallot[r]
        /\ rBallot' = [rBallot EXCEPT ![r] = m.bal]
        /\ rVoted' = [rVoted EXCEPT ![r][m.slot] = [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "AcceptReply", src |-> r, slot |-> m.slot,
                 bal |-> m.bal])
        /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

(* Leader r learns the value for slot s after a quorum of AcceptReplies. *)
Learn(r, s) ==
    /\ lStatus[r][s] = "Accepting"
    /\ \E Q \in Quorums :
         \A q \in Q : \E m \in msgs : /\ m.type = "AcceptReply"
                                      /\ m.src = q
                                      /\ m.slot = s
                                      /\ m.bal = lBallot[r]
    /\ \E am \in msgs :
         /\ am.type = "Accept"
         /\ am.src = r
         /\ am.slot = s
         /\ am.bal = lBallot[r]
         /\ learned' = [learned EXCEPT ![s] = @ \cup {am.val}]
    /\ lStatus' = [lStatus EXCEPT ![r][s] = "Learned"]
    /\ UNCHANGED <<msgs, lBallot, rBallot, rVoted, proposed>>

Next ==
    \/ \E r \in Replicas, b \in Ballots : Prepare(r, b)
    \/ \E r \in Replicas : HandlePrepare(r)
    \/ \E r \in Replicas, s \in Slots, v \in Values : Accept(r, s, v)
    \/ \E r \in Replicas : HandleAccept(r)
    \/ \E r \in Replicas, s \in Slots : Learn(r, s)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

NontrivialityInv == \A s \in Slots : learned[s] \subseteq proposed[s]

ConsistencyInv == \A s \in Slots : Cardinality(learned[s]) <= 1

-----------------------------------------------------------------------------
(* Refinement to ConsensusMulti (abstract spec inlined).                *)
(* Mapping: proposed |-> union of all proposed values,                   *)
(*          learned  |-> learned.                                        *)

absProposed == UNION {proposed[s] : s \in Slots}
absLearned  == learned

AbsInit ==
    /\ absProposed = {}
    /\ absLearned = [s \in Slots |-> {}]

AbsPropose(v) ==
    /\ absProposed' = absProposed \cup {v}
    /\ UNCHANGED absLearned

AbsLearn(s, v) ==
    /\ absLearned[s] = {}
    /\ v \in absProposed
    /\ absLearned' = [absLearned EXCEPT ![s] = {v}]
    /\ UNCHANGED absProposed

AbsNext ==
    \/ \E v \in Values : AbsPropose(v)
    \/ \E s \in Slots, v \in Values : AbsLearn(s, v)

AbsSpec == AbsInit /\ [][AbsNext]_<<absProposed, absLearned>>

(* Check only on very small inputs because of state explosion. *)
ConsensusMultiRefinement == AbsSpec

THEOREM Spec => []TypeOK /\ []NontrivialityInv /\ []ConsistencyInv

-----------------------------------------------------------------------------
(* Symmetry reductions over replicas, values, and slots. *)
SymmetryPerms ==
    Permutations(Replicas) \cup Permutations(Values) \cup Permutations(Slots)

==============================================================================
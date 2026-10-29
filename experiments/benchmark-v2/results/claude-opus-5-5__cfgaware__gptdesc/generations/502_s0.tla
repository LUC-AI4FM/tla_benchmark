---------------------------- MODULE MultiPaxos ----------------------------
(***************************************************************************)
(* Multi-decree Paxos with an aggregated prepare phase.                    *)
(* Every replica is proposer (leader), acceptor and learner at once.       *)
(* A single Prepare message covers all slots. The PrepareReply carries the *)
(* acceptor's votes for every slot. The leader then runs the Accept phase  *)
(* independently per slot. Values are learned per slot via Learn messages. *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ Cardinality(Replicas) >= 3
       /\ Cardinality(Values) >= 2
       /\ Slots # {}
       /\ Ballots # {}
       /\ Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

NoBallot == -1

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

NoVote == [bal |-> NoBallot, val |-> None]

VARIABLES
    lBallot,   \* leader: current ballot of each replica as proposer
    lStatus,   \* leader: "Idle", "Preparing" or "Accepting"
    proposed,  \* leader: per slot, the value to propose (or None if free)
    rBallot,   \* acceptor: highest ballot promised
    rVoted,    \* acceptor: per slot, the last vote [bal, val]
    learned,   \* learner: per slot, the set of learned values
    msgs       \* set of all messages sent

vars == <<lBallot, lStatus, proposed, rBallot, rVoted, learned, msgs>>

Send(m) == msgs' = msgs \cup {m}

----------------------------------------------------------------------------
(* Helper: the safe value for slot s given a set R of PrepareReply msgs   *)
SafeVal(R, s) ==
    LET votes == {m.voted[s] : m \in R} \ {NoVote}
    IN IF votes = {}
          THEN None
          ELSE (CHOOSE vt \in votes : \A w \in votes : w.bal <= vt.bal).val

----------------------------------------------------------------------------
TypeOK ==
    /\ lBallot \in [Replicas -> Ballots \cup {NoBallot}]
    /\ lStatus \in [Replicas -> {"Idle", "Preparing", "Accepting"}]
    /\ proposed \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ rBallot \in [Replicas -> Ballots \cup {NoBallot}]
    /\ rVoted \in [Replicas -> [Slots ->
                     [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]]]
    /\ learned \in [Replicas -> [Slots -> SUBSET Values]]

Init ==
    /\ lBallot  = [r \in Replicas |-> NoBallot]
    /\ lStatus  = [r \in Replicas |-> "Idle"]
    /\ proposed = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ rBallot  = [r \in Replicas |-> NoBallot]
    /\ rVoted   = [r \in Replicas |-> [s \in Slots |-> NoVote]]
    /\ learned  = [r \in Replicas |-> [s \in Slots |-> {}]]
    /\ msgs     = {}

----------------------------------------------------------------------------
(* Leader r starts a new ballot b (aggregated prepare for all slots).     *)
(* Ballots are unique: no other replica may have used b already.          *)
SendPrepare(r, b) ==
    /\ b > lBallot[r]
    /\ ~\E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ lBallot'  = [lBallot EXCEPT ![r] = b]
    /\ lStatus'  = [lStatus EXCEPT ![r] = "Preparing"]
    /\ proposed' = [proposed EXCEPT ![r] = [s \in Slots |-> None]]
    /\ Send([type |-> "Prepare", from |-> r, bal |-> b])
    /\ UNCHANGED <<rBallot, rVoted, learned>>

(* Acceptor a handles a Prepare: promise and report votes for all slots.  *)
HandlePrepare(a) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > rBallot[a]
        /\ rBallot' = [rBallot EXCEPT ![a] = m.bal]
        /\ Send([type  |-> "PrepareReply", from |-> a, to |-> m.from,
                 bal   |-> m.bal, voted |-> rVoted[a]])
        /\ UNCHANGED <<lBallot, lStatus, proposed, rVoted, learned>>

(* Leader r collects PrepareReplies from a quorum and becomes Accepting.  *)
HandlePrepareReplies(r) ==
    /\ lStatus[r] = "Preparing"
    /\ \E Q \in Quorums :
         LET R == {m \in msgs : /\ m.type = "PrepareReply"
                                /\ m.to = r
                                /\ m.bal = lBallot[r]
                                /\ m.from \in Q}
         IN  /\ \A a \in Q : \E m \in R : m.from = a
             /\ proposed' = [proposed EXCEPT ![r] =
                               [s \in Slots |-> SafeVal(R, s)]]
    /\ lStatus' = [lStatus EXCEPT ![r] = "Accepting"]
    /\ UNCHANGED <<lBallot, rBallot, rVoted, learned, msgs>>

(* Leader r sends Accept for slot s with value v (once per ballot/slot).  *)
SendAccept(r, s, v) ==
    /\ lStatus[r] = "Accepting"
    /\ \/ proposed[r][s] = v
       \/ proposed[r][s] = None
    /\ ~\E m \in msgs : /\ m.type = "Accept" /\ m.from = r
                        /\ m.bal = lBallot[r] /\ m.slot = s
    /\ proposed' = [proposed EXCEPT ![r][s] = v]
    /\ Send([type |-> "Accept", from |-> r, bal |-> lBallot[r],
             slot |-> s, val |-> v])
    /\ UNCHANGED <<lBallot, lStatus, rBallot, rVoted, learned>>

(* Acceptor a handles an Accept message.                                  *)
HandleAccept(a) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= rBallot[a]
        /\ rVoted[a][m.slot] # [bal |-> m.bal, val |-> m.val]
        /\ rBallot' = [rBallot EXCEPT ![a] = m.bal]
        /\ rVoted'  = [rVoted EXCEPT ![a][m.slot] =
                          [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "AcceptReply", from |-> a, to |-> m.from,
                 bal |-> m.bal, slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

(* Leader r gathers a quorum of AcceptReplies for slot s; sends Learn.    *)
HandleAcceptReplies(r, s) ==
    /\ lStatus[r] = "Accepting"
    /\ proposed[r][s] # None
    /\ \E Q \in Quorums :
         \A a \in Q :
           \E m \in msgs : /\ m.type = "AcceptReply"
                           /\ m.from = a
                           /\ m.to = r
                           /\ m.bal = lBallot[r]
                           /\ m.slot = s
                           /\ m.val = proposed[r][s]
    /\ Send([type |-> "Learn", from |-> r, slot |-> s, val |-> proposed[r][s]])
    /\ UNCHANGED <<lBallot, lStatus, proposed, rBallot, rVoted, learned>>

(* Learner a learns a value for a slot.                                   *)
HandleLearn(a) ==
    \E m \in msgs :
        /\ m.type = "Learn"
        /\ m.val \notin learned[a][m.slot]
        /\ learned' = [learned EXCEPT ![a][m.slot] = @ \cup {m.val}]
        /\ UNCHANGED <<lBallot, lStatus, proposed, rBallot, rVoted, msgs>>

(* Allow stuttering once nothing else is possible (as in PlusCal).        *)
Terminating == UNCHANGED vars

Next ==
    \/ \E r \in Replicas, b \in Ballots : SendPrepare(r, b)
    \/ \E a \in Replicas : HandlePrepare(a)
    \/ \E r \in Replicas : HandlePrepareReplies(r)
    \/ \E r \in Replicas, s \in Slots, v \in Values : SendAccept(r, s, v)
    \/ \E a \in Replicas : HandleAccept(a)
    \/ \E r \in Replicas, s \in Slots : HandleAcceptReplies(r, s)
    \/ \E a \in Replicas : HandleLearn(a)
    \/ Terminating

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(* Safety: at most one value is learned per slot, across all replicas.    *)
Agreement ==
    \A s \in Slots :
        \A r1, r2 \in Replicas :
            \A v1 \in learned[r1][s], v2 \in learned[r2][s] : v1 = v2

Consistency == \A r \in Replicas, s \in Slots : Cardinality(learned[r][s]) <= 1

=============================================================================
------------------------------- MODULE MultiPaxos -------------------------------
(***************************************************************************)
(* Multi-decree Paxos with an aggregated prepare phase.                    *)
(* Each replica acts as proposer, acceptor and learner.  A single Prepare  *)
(* message covers all slots.  The PrepareReply carries the acceptor's      *)
(* accepted (ballot, value) pair for every slot.  Accept, AcceptReply and  *)
(* Learn messages are per slot.  Quorums are majorities of replicas.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ IsFiniteSet(Replicas) /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Values)   /\ Cardinality(Values) >= 2
       /\ IsFiniteSet(Slots)    /\ Slots # {}
       /\ IsFiniteSet(Ballots)  /\ Ballots # {} /\ Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

\* Fixed injective ranking of replicas, used to break ballot ties.
Rank == CHOOSE f \in [Replicas -> 1..Cardinality(Replicas)] :
          \A x, y \in Replicas : f[x] = f[y] => x = y

\* A ballot is a (number, owner) pair; ballots are totally ordered.
BallotSet == [num : Ballots, id : Replicas]
Bottom == [num |-> -1, id |-> CHOOSE r \in Replicas : TRUE]
AllBallots == BallotSet \cup {Bottom}

Gt(b1, b2) == \/ b1.num > b2.num
              \/ /\ b1.num = b2.num
                 /\ Rank[b1.id] > Rank[b2.id]

Geq(b1, b2) == b1 = b2 \/ Gt(b1, b2)

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

NoAccept == [bal |-> Bottom, val |-> None]
AcceptedRec == [bal : AllBallots, val : Values \cup {None}]

VARIABLES
    msgs,        \* set of all messages sent
    promised,    \* promised[a] : highest ballot acceptor a has promised
    accepted,    \* accepted[a][s] : [bal, val] last accepted in slot s
    pBal,        \* pBal[r] : ballot proposer r is currently using
    pPhase,      \* pPhase[r] \in {"idle", "preparing", "leading"}
    pSafe,       \* pSafe[r][s] : value forced by prepare phase, or None
    pProposed,   \* pProposed[r][s] : value proposed in current ballot, or None
    learned      \* learned[r][s] : set of values learned for slot s

vars == <<msgs, promised, accepted, pBal, pPhase, pSafe, pProposed, learned>>

PrepareMsg == [type : {"prepare"}, from : Replicas, bal : BallotSet]
PrepareReplyMsg == [type : {"preparereply"}, from : Replicas, to : Replicas,
                    bal : BallotSet, accepted : [Slots -> AcceptedRec]]
AcceptMsg == [type : {"accept"}, from : Replicas, bal : BallotSet,
              slot : Slots, val : Values]
AcceptReplyMsg == [type : {"acceptreply"}, from : Replicas, to : Replicas,
                   bal : BallotSet, slot : Slots]
LearnMsg == [type : {"learn"}, from : Replicas, slot : Slots, val : Values]

Messages == PrepareMsg \cup PrepareReplyMsg \cup AcceptMsg
            \cup AcceptReplyMsg \cup LearnMsg

TypeOK ==
    /\ msgs \subseteq Messages
    /\ promised \in [Replicas -> AllBallots]
    /\ accepted \in [Replicas -> [Slots -> AcceptedRec]]
    /\ pBal \in [Replicas -> AllBallots]
    /\ pPhase \in [Replicas -> {"idle", "preparing", "leading"}]
    /\ pSafe \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ pProposed \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ learned \in [Replicas -> [Slots -> SUBSET Values]]

Init ==
    /\ msgs = {}
    /\ promised = [a \in Replicas |-> Bottom]
    /\ accepted = [a \in Replicas |-> [s \in Slots |-> NoAccept]]
    /\ pBal = [r \in Replicas |-> Bottom]
    /\ pPhase = [r \in Replicas |-> "idle"]
    /\ pSafe = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ pProposed = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ learned = [r \in Replicas |-> [s \in Slots |-> {}]]

(***************************************************************************)
(* Proposer: start a new ballot and send an aggregated Prepare.            *)
(***************************************************************************)
SendPrepare(r, n) ==
    LET b == [num |-> n, id |-> r] IN
    /\ Gt(b, pBal[r])
    /\ pBal' = [pBal EXCEPT ![r] = b]
    /\ pPhase' = [pPhase EXCEPT ![r] = "preparing"]
    /\ pSafe' = [pSafe EXCEPT ![r] = [s \in Slots |-> None]]
    /\ pProposed' = [pProposed EXCEPT ![r] = [s \in Slots |-> None]]
    /\ msgs' = msgs \cup {[type |-> "prepare", from |-> r, bal |-> b]}
    /\ UNCHANGED <<promised, accepted, learned>>

(***************************************************************************)
(* Acceptor: handle Prepare, reply with accepted info for all slots.       *)
(***************************************************************************)
HandlePrepare(a, m) ==
    /\ m.type = "prepare"
    /\ Gt(m.bal, promised[a])
    /\ promised' = [promised EXCEPT ![a] = m.bal]
    /\ msgs' = msgs \cup {[type |-> "preparereply", from |-> a, to |-> m.from,
                           bal |-> m.bal, accepted |-> accepted[a]]}
    /\ UNCHANGED <<accepted, pBal, pPhase, pSafe, pProposed, learned>>

\* Value with the highest accepted ballot for slot s among replies R.
SafeVal(R, s) ==
    LET accs == {m.accepted[s] : m \in R} \ {NoAccept}
    IN IF accs = {} THEN None
       ELSE (CHOOSE x \in accs : \A y \in accs : Geq(x.bal, y.bal)).val

(***************************************************************************)
(* Proposer: handle PrepareReplies from a majority quorum.                 *)
(***************************************************************************)
HandlePrepareReplies(r, Q) ==
    LET R == {m \in msgs : /\ m.type = "preparereply"
                           /\ m.to = r
                           /\ m.bal = pBal[r]
                           /\ m.from \in Q}
    IN
    /\ pPhase[r] = "preparing"
    /\ {m.from : m \in R} = Q
    /\ pPhase' = [pPhase EXCEPT ![r] = "leading"]
    /\ pSafe' = [pSafe EXCEPT ![r] = [s \in Slots |-> SafeVal(R, s)]]
    /\ UNCHANGED <<msgs, promised, accepted, pBal, pProposed, learned>>

(***************************************************************************)
(* Proposer (leader): send Accept for a slot.                              *)
(***************************************************************************)
SendAccept(r, s, v) ==
    /\ pPhase[r] = "leading"
    /\ pProposed[r][s] = None
    /\ pSafe[r][s] # None => v = pSafe[r][s]
    /\ pProposed' = [pProposed EXCEPT ![r][s] = v]
    /\ msgs' = msgs \cup {[type |-> "accept", from |-> r, bal |-> pBal[r],
                           slot |-> s, val |-> v]}
    /\ UNCHANGED <<promised, accepted, pBal, pPhase, pSafe, learned>>

(***************************************************************************)
(* Acceptor: handle Accept.                                                *)
(***************************************************************************)
HandleAccept(a, m) ==
    /\ m.type = "accept"
    /\ Geq(m.bal, promised[a])
    /\ promised' = [promised EXCEPT ![a] = m.bal]
    /\ accepted' = [accepted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
    /\ msgs' = msgs \cup {[type |-> "acceptreply", from |-> a, to |-> m.from,
                           bal |-> m.bal, slot |-> m.slot]}
    /\ UNCHANGED <<pBal, pPhase, pSafe, pProposed, learned>>

(***************************************************************************)
(* Proposer: handle AcceptReplies from a majority quorum; send Learn.      *)
(***************************************************************************)
HandleAcceptReplies(r, s, Q) ==
    LET R == {m \in msgs : /\ m.type = "acceptreply"
                           /\ m.to = r
                           /\ m.bal = pBal[r]
                           /\ m.slot = s
                           /\ m.from \in Q}
    IN
    /\ pPhase[r] = "leading"
    /\ pProposed[r][s] # None
    /\ {m.from : m \in R} = Q
    /\ msgs' = msgs \cup {[type |-> "learn", from |-> r, slot |-> s,
                           val |-> pProposed[r][s]]}
    /\ UNCHANGED <<promised, accepted, pBal, pPhase, pSafe, pProposed, learned>>

(***************************************************************************)
(* Learner: handle Learn.                                                  *)
(***************************************************************************)
HandleLearn(r, m) ==
    /\ m.type = "learn"
    /\ m.val \notin learned[r][m.slot]
    /\ learned' = [learned EXCEPT ![r][m.slot] = @ \cup {m.val}]
    /\ UNCHANGED <<msgs, promised, accepted, pBal, pPhase, pSafe, pProposed>>

Next ==
    \/ \E r \in Replicas, n \in Ballots : SendPrepare(r, n)
    \/ \E a \in Replicas, m \in msgs : HandlePrepare(a, m)
    \/ \E r \in Replicas, Q \in Quorums : HandlePrepareReplies(r, Q)
    \/ \E r \in Replicas, s \in Slots, v \in Values : SendAccept(r, s, v)
    \/ \E a \in Replicas, m \in msgs : HandleAccept(a, m)
    \/ \E r \in Replicas, s \in Slots, Q \in Quorums : HandleAcceptReplies(r, s, Q)
    \/ \E r \in Replicas, m \in msgs : HandleLearn(r, m)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Each replica learns at most one value per slot.
LearnedAtMostOne ==
    \A r \in Replicas, s \in Slots : Cardinality(learned[r][s]) <= 1

\* No two replicas learn different values for the same slot.
Agreement ==
    \A r1, r2 \in Replicas, s \in Slots :
        \A v1 \in learned[r1][s], v2 \in learned[r2][s] : v1 = v2

\* All values ever chosen for a slot (via Learn messages) agree.
Consistency ==
    \A m1, m2 \in msgs :
        (m1.type = "learn" /\ m2.type = "learn" /\ m1.slot = m2.slot)
            => m1.val = m2.val

\* Only proposed values can be learned.
Nontriviality ==
    \A r \in Replicas, s \in Slots : learned[r][s] \subseteq Values

THEOREM Spec => [](TypeOK /\ LearnedAtMostOne /\ Agreement /\ Consistency /\ Nontriviality)
=============================================================================
------------------------------- MODULE MultiPaxos -------------------------------
(***************************************************************************)
(* Multi-decree Paxos with an aggregated prepare phase.                    *)
(* Every replica acts as proposer, acceptor and learner.  A single        *)
(* Prepare message for ballot b covers all slots.  Each PrepareReply      *)
(* carries the acceptor's full per-slot accepted state.  After a majority *)
(* of PrepareReplies, the proposer issues Accept messages slot by slot.   *)
(* Majorities of AcceptReplies lead to Learn messages, which update the   *)
(* learned values per slot.                                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ IsFiniteSet(Replicas) /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Values)   /\ Cardinality(Values) >= 2
       /\ IsFiniteSet(Slots)    /\ Slots # {}
       /\ IsFiniteSet(Ballots)  /\ Ballots # {} /\ Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

NoBallot == -1

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

AcceptedEntry == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]

EmptyEntry == [bal |-> NoBallot, val |-> None]

PrepareMsg      == [type : {"prepare"}, from : Replicas, bal : Ballots]
PrepareReplyMsg == [type : {"prepareReply"}, from : Replicas, to : Replicas,
                    bal : Ballots, accepted : [Slots -> AcceptedEntry]]
AcceptMsg       == [type : {"accept"}, from : Replicas, bal : Ballots,
                    slot : Slots, val : Values]
AcceptReplyMsg  == [type : {"acceptReply"}, from : Replicas, to : Replicas,
                    bal : Ballots, slot : Slots, val : Values]
LearnMsg        == [type : {"learn"}, from : Replicas, slot : Slots, val : Values]

Messages == PrepareMsg \cup PrepareReplyMsg \cup AcceptMsg
              \cup AcceptReplyMsg \cup LearnMsg

VARIABLES
    msgs,       \* set of all messages ever sent
    maxBal,     \* maxBal[r] : highest ballot promised by replica r
    accepted,   \* accepted[r][s] : highest-ballot accepted (bal, val) at r for slot s
    learned     \* learned[r][s] : set of values learned by r for slot s

vars == <<msgs, maxBal, accepted, learned>>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Replicas -> Ballots \cup {NoBallot}]
    /\ accepted \in [Replicas -> [Slots -> AcceptedEntry]]
    /\ learned \in [Replicas -> [Slots -> SUBSET Values]]

Init ==
    /\ msgs = {}
    /\ maxBal = [r \in Replicas |-> NoBallot]
    /\ accepted = [r \in Replicas |-> [s \in Slots |-> EmptyEntry]]
    /\ learned = [r \in Replicas |-> [s \in Slots |-> {}]]

(***************************************************************************)
(* Proposer r starts ballot b with one aggregated Prepare for all slots.   *)
(* Each ballot is used by at most one proposer.                            *)
(***************************************************************************)
SendPrepare(r, b) ==
    /\ ~\E m \in msgs : m.type = "prepare" /\ m.bal = b
    /\ Send([type |-> "prepare", from |-> r, bal |-> b])
    /\ UNCHANGED <<maxBal, accepted, learned>>

(***************************************************************************)
(* Acceptor a handles a Prepare.  It promises the ballot and replies with  *)
(* its accepted state for every slot.                                      *)
(***************************************************************************)
HandlePrepare(a) ==
    \E m \in msgs :
        /\ m.type = "prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "prepareReply", from |-> a, to |-> m.from,
                 bal |-> m.bal, accepted |-> accepted[a]])
        /\ UNCHANGED <<accepted, learned>>

(***************************************************************************)
(* Proposer r has a majority of PrepareReplies for its ballot b.  It sends *)
(* an Accept for slot s.  The value is the highest-ballot accepted value   *)
(* reported for s; if none was reported, the value is any value.           *)
(***************************************************************************)
SendAccept(r, b, s) ==
    /\ \E m \in msgs : m.type = "prepare" /\ m.from = r /\ m.bal = b
    /\ ~\E m \in msgs : m.type = "accept" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
        LET R == {m \in msgs : /\ m.type = "prepareReply"
                               /\ m.to = r
                               /\ m.bal = b
                               /\ m.from \in Q}
        IN /\ \A q \in Q : \E m \in R : m.from = q
           /\ LET acc == {m.accepted[s] : m \in R}
                  hb  == CHOOSE x \in acc : \A y \in acc : y.bal <= x.bal
              IN IF hb.bal = NoBallot
                   THEN \E v \in Values :
                          Send([type |-> "accept", from |-> r, bal |-> b,
                                slot |-> s, val |-> v])
                   ELSE Send([type |-> "accept", from |-> r, bal |-> b,
                              slot |-> s, val |-> hb.val])
    /\ UNCHANGED <<maxBal, accepted, learned>>

(***************************************************************************)
(* Acceptor a handles an Accept message whose ballot is at least as high   *)
(* as its promise.                                                         *)
(***************************************************************************)
HandleAccept(a) ==
    \E m \in msgs :
        /\ m.type = "accept"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ accepted' = [accepted EXCEPT ![a][m.slot] =
                            [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "acceptReply", from |-> a, to |-> m.from,
                 bal |-> m.bal, slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED learned

(***************************************************************************)
(* Proposer r has a majority of AcceptReplies for (b, s, v).  It            *)
(* broadcasts a Learn message.                                             *)
(***************************************************************************)
SendLearn(r) ==
    \E b \in Ballots, s \in Slots, v \in Values, Q \in Quorums :
        /\ \A q \in Q : \E m \in msgs : /\ m.type = "acceptReply"
                                        /\ m.from = q
                                        /\ m.to = r
                                        /\ m.bal = b
                                        /\ m.slot = s
                                        /\ m.val = v
        /\ Send([type |-> "learn", from |-> r, slot |-> s, val |-> v])
        /\ UNCHANGED <<maxBal, accepted, learned>>

(***************************************************************************)
(* Learner a handles a Learn message.                                      *)
(***************************************************************************)
HandleLearn(a) ==
    \E m \in msgs :
        /\ m.type = "learn"
        /\ m.val \notin learned[a][m.slot]
        /\ learned' = [learned EXCEPT ![a][m.slot] = @ \cup {m.val}]
        /\ UNCHANGED <<msgs, maxBal, accepted>>

Replica(r) ==
    \/ \E b \in Ballots : SendPrepare(r, b)
    \/ HandlePrepare(r)
    \/ \E b \in Ballots, s \in Slots : SendAccept(r, b, s)
    \/ HandleAccept(r)
    \/ SendLearn(r)
    \/ HandleLearn(r)

Next == \E r \in Replicas : Replica(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

\* Each replica learns at most one value per slot.
SingleLearned ==
    \A r \in Replicas, s \in Slots : Cardinality(learned[r][s]) <= 1

\* No two replicas learn different values for the same slot.
Agreement ==
    \A r1, r2 \in Replicas, s \in Slots :
        \A v1 \in learned[r1][s], v2 \in learned[r2][s] : v1 = v2

\* Every learned value was proposed in some Accept message.
Validity ==
    \A r \in Replicas, s \in Slots, v \in Values :
        v \in learned[r][s] =>
            \E m \in msgs : m.type = "accept" /\ m.slot = s /\ m.val = v

\* Within a ballot and slot, at most one value is proposed.
UniqueAcceptPerBallot ==
    \A m1, m2 \in msgs :
        (m1.type = "accept" /\ m2.type = "accept"
           /\ m1.bal = m2.bal /\ m1.slot = m2.slot) => m1.val = m2.val

Inv == TypeOK /\ SingleLearned /\ Agreement /\ Validity /\ UniqueAcceptPerBallot

THEOREM Spec => []Inv
=============================================================================
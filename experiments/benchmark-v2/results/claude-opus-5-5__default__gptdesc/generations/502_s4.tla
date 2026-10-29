------------------------------- MODULE MultiPaxos -------------------------------
(***************************************************************************)
(* Multi-decree Paxos with an aggregated prepare phase.                    *)
(*                                                                         *)
(* Every replica acts as proposer, acceptor and learner. A single Prepare  *)
(* message for a ballot covers all slots. Each PrepareReply returns the    *)
(* acceptor's accepted (ballot, value) pair for every slot. After that,    *)
(* the proposer runs the Accept phase separately for each slot.            *)
(*                                                                         *)
(* Messages are kept in a monotonically growing set, so the network may    *)
(* lose, duplicate or reorder them.                                        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Replicas,   \* set of replicas (proposer + acceptor + learner)
          Values,     \* set of values that may be proposed
          Slots,      \* set of log slots (consensus instances)
          Ballots     \* set of ballot numbers

ASSUME /\ IsFiniteSet(Replicas)
       /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Values)
       /\ Cardinality(Values) >= 2
       /\ IsFiniteSet(Slots)
       /\ Slots # {}
       /\ IsFiniteSet(Ballots)
       /\ Ballots # {}
       /\ Ballots \subseteq Nat

None == CHOOSE v : v \notin Values

NoBallot == -1

\* Majority quorums: any two of them intersect.
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

\* An accepted (ballot, value) pair for one slot.
Vote == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]

NoVote == [bal |-> NoBallot, val |-> None]

PrepareMsg      == [type : {"prepare"}, from : Replicas, bal : Ballots]
PrepareReplyMsg == [type : {"prepareReply"}, from : Replicas, to : Replicas,
                    bal : Ballots, voted : [Slots -> Vote]]
AcceptMsg       == [type : {"accept"}, from : Replicas, bal : Ballots,
                    slot : Slots, val : Values]
AcceptReplyMsg  == [type : {"acceptReply"}, from : Replicas, to : Replicas,
                    bal : Ballots, slot : Slots, val : Values]
LearnMsg        == [type : {"learn"}, from : Replicas, slot : Slots, val : Values]

Messages == PrepareMsg \cup PrepareReplyMsg \cup AcceptMsg
              \cup AcceptReplyMsg \cup LearnMsg

VARIABLES msgs,      \* set of all messages sent so far
          maxBal,    \* maxBal[r]: highest ballot r has promised or accepted in
          accepted,  \* accepted[r][s]: last vote r cast in slot s
          learned    \* learned[r][s]: set of values r has learned for slot s

vars == <<msgs, maxBal, accepted, learned>>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Replicas -> Ballots \cup {NoBallot}]
    /\ accepted \in [Replicas -> [Slots -> Vote]]
    /\ learned \in [Replicas -> [Slots -> SUBSET Values]]

Init ==
    /\ msgs = {}
    /\ maxBal = [r \in Replicas |-> NoBallot]
    /\ accepted = [r \in Replicas |-> [s \in Slots |-> NoVote]]
    /\ learned = [r \in Replicas |-> [s \in Slots |-> {}]]

(***************************************************************************)
(* Proposer r starts ballot b by sending one aggregated Prepare for all    *)
(* slots. Ballots are unique: at most one replica may ever use ballot b.   *)
(***************************************************************************)
SendPrepare(r, b) ==
    /\ ~ \E m \in msgs : m.type = "prepare" /\ m.bal = b
    /\ Send([type |-> "prepare", from |-> r, bal |-> b])
    /\ UNCHANGED <<maxBal, accepted, learned>>

(***************************************************************************)
(* Acceptor r handles a Prepare. It promises the ballot and replies with   *)
(* its accepted votes for all slots.                                       *)
(***************************************************************************)
HandlePrepare(r, m) ==
    /\ m.type = "prepare"
    /\ m.bal > maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
    /\ Send([type |-> "prepareReply", from |-> r, to |-> m.from,
             bal |-> m.bal, voted |-> accepted[r]])
    /\ UNCHANGED <<accepted, learned>>

(***************************************************************************)
(* Proposer r has received PrepareReplies for ballot b from a majority     *)
(* quorum Q. It then sends an Accept for slot s. It must choose the value  *)
(* with the highest ballot reported for s. If no value was reported, it    *)
(* may choose any value.                                                   *)
(***************************************************************************)
SendAccept(r, b, s) ==
    /\ \E m \in msgs : m.type = "prepare" /\ m.from = r /\ m.bal = b
    /\ ~ \E m \in msgs : m.type = "accept" /\ m.from = r
                         /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums :
         LET replies == {m \in msgs : /\ m.type = "prepareReply"
                                      /\ m.to = r
                                      /\ m.bal = b
                                      /\ m.from \in Q}
             votes   == {m.voted[s] : m \in replies} \ {NoVote}
         IN  /\ \A q \in Q : \E m \in replies : m.from = q
             /\ IF votes = {}
                  THEN \E v \in Values :
                         Send([type |-> "accept", from |-> r, bal |-> b,
                               slot |-> s, val |-> v])
                  ELSE LET best == CHOOSE x \in votes :
                                     \A y \in votes : y.bal <= x.bal
                       IN  Send([type |-> "accept", from |-> r, bal |-> b,
                                 slot |-> s, val |-> best.val])
    /\ UNCHANGED <<maxBal, accepted, learned>>

(***************************************************************************)
(* Acceptor r handles an Accept. It only accepts if it has not promised a  *)
(* higher ballot.                                                          *)
(***************************************************************************)
HandleAccept(r, m) ==
    /\ m.type = "accept"
    /\ m.bal >= maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
    /\ accepted' = [accepted EXCEPT ![r][m.slot] = [bal |-> m.bal, val |-> m.val]]
    /\ Send([type |-> "acceptReply", from |-> r, to |-> m.from,
             bal |-> m.bal, slot |-> m.slot, val |-> m.val])
    /\ UNCHANGED learned

(***************************************************************************)
(* Proposer r has received AcceptReplies for (b, s, v) from a majority.    *)
(* The value is now chosen, so r broadcasts a Learn message.               *)
(***************************************************************************)
SendLearn(r, b, s, v) ==
    /\ \E Q \in Quorums :
         \A q \in Q : \E m \in msgs : /\ m.type = "acceptReply"
                                      /\ m.from = q
                                      /\ m.to = r
                                      /\ m.bal = b
                                      /\ m.slot = s
                                      /\ m.val = v
    /\ ~ \E m \in msgs : m.type = "learn" /\ m.from = r
                         /\ m.slot = s /\ m.val = v
    /\ Send([type |-> "learn", from |-> r, slot |-> s, val |-> v])
    /\ UNCHANGED <<maxBal, accepted, learned>>

(***************************************************************************)
(* Learner r handles a Learn message.                                      *)
(***************************************************************************)
HandleLearn(r, m) ==
    /\ m.type = "learn"
    /\ m.val \notin learned[r][m.slot]
    /\ learned' = [learned EXCEPT ![r][m.slot] = @ \cup {m.val}]
    /\ UNCHANGED <<msgs, maxBal, accepted>>

Next ==
    \/ \E r \in Replicas, b \in Ballots : SendPrepare(r, b)
    \/ \E r \in Replicas, m \in msgs : HandlePrepare(r, m)
    \/ \E r \in Replicas, b \in Ballots, s \in Slots : SendAccept(r, b, s)
    \/ \E r \in Replicas, m \in msgs : HandleAccept(r, m)
    \/ \E r \in Replicas, b \in Ballots, s \in Slots, v \in Values :
         SendLearn(r, b, s, v)
    \/ \E r \in Replicas, m \in msgs : HandleLearn(r, m)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* All replicas learn at most one value per slot (Agreement).
Agreement ==
    \A s \in Slots : \A r1, r2 \in Replicas :
        \A v1 \in learned[r1][s], v2 \in learned[r2][s] : v1 = v2

\* Every learned value was proposed (Validity / Nontriviality).
Validity ==
    \A r \in Replicas, s \in Slots : \A v \in learned[r][s] :
        \E m \in msgs : m.type = "accept" /\ m.slot = s /\ m.val = v

\* Every Learn message carries a value that is the only one learnable for its slot.
LearnMsgsAgree ==
    \A m1, m2 \in msgs :
        (m1.type = "learn" /\ m2.type = "learn" /\ m1.slot = m2.slot)
            => m1.val = m2.val

\* In each ballot, each slot has at most one proposed value.
OneValuePerBallotSlot ==
    \A m1, m2 \in msgs :
        (/\ m1.type = "accept" /\ m2.type = "accept"
         /\ m1.bal = m2.bal /\ m1.slot = m2.slot)
            => m1.val = m2.val

Inv == TypeOK /\ Agreement /\ Validity /\ LearnMsgsAgree /\ OneValuePerBallotSlot

THEOREM Spec => []Inv
=============================================================================
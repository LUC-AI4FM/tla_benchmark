---------------------------- MODULE MultiPaxosAggregated ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ Cardinality(Replicas) >= 3
       /\ Cardinality(Values) >= 2
       /\ Slots # {}
       /\ Ballots # {}
       /\ Ballots \subseteq (Nat \ {0})
       /\ IsFiniteSet(Replicas)
       /\ IsFiniteSet(Values)
       /\ IsFiniteSet(Slots)
       /\ IsFiniteSet(Ballots)

None == CHOOSE v : v \notin Values

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

NoEntry == [bal |-> 0, val |-> None]

Entry == [bal : Ballots \cup {0}, val : Values \cup {None}]

VARIABLES
    msgs,       \* set of all messages ever sent
    ballot,     \* ballot[r]: highest ballot seen/promised by replica r
    leader,     \* leader[r]: TRUE iff r has completed phase 1 for ballot[r]
    proposals,  \* proposals[r][s]: value forced by phase 1 for slot s, or None
    accepted,   \* accepted[r][s]: [bal, val] last accepted by r for slot s
    learned     \* learned[r][s]: value learned by r for slot s, or None

vars == <<msgs, ballot, leader, proposals, accepted, learned>>

TypeOK ==
    /\ ballot \in [Replicas -> Ballots \cup {0}]
    /\ leader \in [Replicas -> BOOLEAN]
    /\ proposals \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ accepted \in [Replicas -> [Slots -> Entry]]
    /\ learned \in [Replicas -> [Slots -> Values \cup {None}]]

Send(m) == msgs' = msgs \cup {m}

MaxEntry(S) == CHOOSE e \in S : \A f \in S : f.bal <= e.bal

Init ==
    /\ msgs = {}
    /\ ballot = [r \in Replicas |-> 0]
    /\ leader = [r \in Replicas |-> FALSE]
    /\ proposals = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ accepted = [r \in Replicas |-> [s \in Slots |-> NoEntry]]
    /\ learned = [r \in Replicas |-> [s \in Slots |-> None]]

-----------------------------------------------------------------------------
(* Phase 1a: a proposer sends an aggregated Prepare covering all slots. *)
SendPrepare(r) ==
    \E b \in Ballots :
        /\ b > ballot[r]
        /\ ~\E m \in msgs : m.type = "prepare" /\ m.bal = b
        /\ Send([type |-> "prepare", from |-> r, bal |-> b])
        /\ UNCHANGED <<ballot, leader, proposals, accepted, learned>>

(* Phase 1b: an acceptor promises and reports accepted entries for all slots. *)
HandlePrepare(a) ==
    \E m \in msgs :
        /\ m.type = "prepare"
        /\ m.bal > ballot[a]
        /\ ballot' = [ballot EXCEPT ![a] = m.bal]
        /\ leader' = [leader EXCEPT ![a] = FALSE]
        /\ Send([type |-> "preparereply", from |-> a, to |-> m.from,
                 bal |-> m.bal, acc |-> accepted[a]])
        /\ UNCHANGED <<proposals, accepted, learned>>

(* A proposer collecting a majority of PrepareReplies becomes leader. *)
HandlePrepareReply(r) ==
    /\ ~leader[r]
    /\ ballot[r] # 0
    /\ \E m \in msgs : m.type = "prepare" /\ m.from = r /\ m.bal = ballot[r]
    /\ \E Q \in Quorums :
         LET Replies == {m \in msgs : /\ m.type = "preparereply"
                                      /\ m.to = r
                                      /\ m.bal = ballot[r]
                                      /\ m.from \in Q}
         IN  /\ \A q \in Q : \E m \in Replies : m.from = q
             /\ proposals' = [proposals EXCEPT ![r] =
                  [s \in Slots |->
                     LET E == {m.acc[s] : m \in Replies}
                     IN  IF \E e \in E : e.bal > 0
                            THEN MaxEntry(E).val
                            ELSE None]]
    /\ leader' = [leader EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<msgs, ballot, accepted, learned>>

(* Phase 2a: the leader proposes a value for a slot. *)
SendAccept(r) ==
    \E s \in Slots, v \in Values :
        /\ leader[r]
        /\ ~\E m \in msgs : /\ m.type = "accept" /\ m.from = r
                            /\ m.bal = ballot[r] /\ m.slot = s
        /\ proposals[r][s] = None \/ proposals[r][s] = v
        /\ Send([type |-> "accept", from |-> r, bal |-> ballot[r],
                 slot |-> s, val |-> v])
        /\ UNCHANGED <<ballot, leader, proposals, accepted, learned>>

(* Phase 2b: an acceptor accepts if it has not promised a higher ballot. *)
HandleAccept(a) ==
    \E m \in msgs :
        /\ m.type = "accept"
        /\ m.bal >= ballot[a]
        /\ ballot' = [ballot EXCEPT ![a] = m.bal]
        /\ leader' = [leader EXCEPT ![a] = IF m.bal > ballot[a] THEN FALSE
                                                                ELSE leader[a]]
        /\ accepted' = [accepted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "acceptreply", from |-> a, to |-> m.from,
                 bal |-> m.bal, slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<proposals, learned>>

(* The leader, upon a majority of AcceptReplies, broadcasts Learn. *)
HandleAcceptReply(r) ==
    \E s \in Slots, v \in Values :
        /\ leader[r]
        /\ \E Q \in Quorums :
             \A q \in Q : \E m \in msgs : /\ m.type = "acceptreply"
                                          /\ m.from = q
                                          /\ m.to = r
                                          /\ m.bal = ballot[r]
                                          /\ m.slot = s
                                          /\ m.val = v
        /\ Send([type |-> "learn", from |-> r, slot |-> s, val |-> v])
        /\ UNCHANGED <<ballot, leader, proposals, accepted, learned>>

(* Learners record decided values. *)
HandleLearn(a) ==
    \E m \in msgs :
        /\ m.type = "learn"
        /\ learned[a][m.slot] = None
        /\ learned' = [learned EXCEPT ![a][m.slot] = m.val]
        /\ UNCHANGED <<msgs, ballot, leader, proposals, accepted>>

-----------------------------------------------------------------------------
Next ==
    \E r \in Replicas :
        \/ SendPrepare(r)
        \/ HandlePrepare(r)
        \/ HandlePrepareReply(r)
        \/ SendAccept(r)
        \/ HandleAccept(r)
        \/ HandleAcceptReply(r)
        \/ HandleLearn(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)
Validity ==
    \A r \in Replicas, s \in Slots : learned[r][s] \in Values \cup {None}

Agreement ==
    \A r1, r2 \in Replicas, s \in Slots :
        (learned[r1][s] # None /\ learned[r2][s] # None)
            => learned[r1][s] = learned[r2][s]

LearnMsgConsistency ==
    \A m1, m2 \in msgs :
        (m1.type = "learn" /\ m2.type = "learn" /\ m1.slot = m2.slot)
            => m1.val = m2.val

Safety == TypeOK /\ Validity /\ Agreement /\ LearnMsgConsistency

THEOREM Spec => []Safety
=============================================================================
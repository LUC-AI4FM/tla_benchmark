---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ASSUME /\ Cardinality(Replicas) >= 3
       /\ Cardinality(Values) >= 2
       /\ 0 \notin Values
       /\ Slots # {}
       /\ IsFiniteSet(Slots)
       /\ Ballots # {}
       /\ Ballots \subseteq Nat
       /\ IsFiniteSet(Ballots)

VARIABLES msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned

vars == <<msgs, lBallot, lStatus, rBallot, rVoted, proposed, learned>>

NoBallot == -1
NoValue  == 0

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

Send(m) == msgs' = msgs \cup {m}

Init ==
    /\ msgs = {}
    /\ lBallot = [r \in Replicas |-> NoBallot]
    /\ lStatus = [r \in Replicas |-> [s \in Slots |-> ""]]
    /\ rBallot = [r \in Replicas |-> NoBallot]
    /\ rVoted = [r \in Replicas |-> [s \in Slots |-> [bal |-> NoBallot, val |-> NoValue]]]
    /\ proposed = [s \in Slots |-> {}]
    /\ learned = [s \in Slots |-> {}]

-----------------------------------------------------------------------------
(* Phase 1a: leader r picks a fresh higher ballot and prepares all slots. *)
Prepare(r) ==
    \E b \in Ballots :
        /\ b > lBallot[r]
        /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
        /\ lBallot' = [lBallot EXCEPT ![r] = b]
        /\ lStatus' = [lStatus EXCEPT ![r] =
                          [s \in Slots |-> IF lStatus[r][s] = "Learned"
                                              THEN "Learned"
                                              ELSE "Preparing"]]
        /\ Send([type |-> "Prepare", from |-> r, bal |-> b])
        /\ UNCHANGED <<rBallot, rVoted, proposed, learned>>

(* Phase 1b: acceptor a promises and returns its full voted record. *)
PrepareReply(a) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > rBallot[a]
        /\ rBallot' = [rBallot EXCEPT ![a] = m.bal]
        /\ Send([type |-> "PrepareReply", from |-> a, to |-> m.from,
                 bal |-> m.bal, voted |-> rVoted[a]])
        /\ UNCHANGED <<lBallot, lStatus, rVoted, proposed, learned>>

(* v is safe to propose in slot s given the set M of prepare replies. *)
ValuePreparedIn(M, s, v) ==
    LET votes   == {m.voted[s] : m \in M}
        bals    == {vt.bal : vt \in votes} \cup {NoBallot}
        maxBal  == CHOOSE x \in bals : \A y \in bals : y <= x
    IN  IF maxBal = NoBallot
           THEN TRUE
           ELSE \E vt \in votes : vt.bal = maxBal /\ vt.val = v

(* Phase 2a: leader r, preparing slot s, gathers a quorum and proposes. *)
Accept(r) ==
    \E s \in Slots :
        /\ lStatus[r][s] = "Preparing"
        /\ \E Q \in Quorums :
             LET replies == {m \in msgs : /\ m.type = "PrepareReply"
                                          /\ m.to = r
                                          /\ m.bal = lBallot[r]
                                          /\ m.from \in Q}
             IN  /\ \A a \in Q : \E m \in replies : m.from = a
                 /\ \E v \in Values :
                      /\ ValuePreparedIn(replies, s, v)
                      /\ Send([type |-> "Accept", from |-> r, bal |-> lBallot[r],
                               slot |-> s, val |-> v])
                      /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
        /\ lStatus' = [lStatus EXCEPT ![r][s] = "Accepting"]
        /\ UNCHANGED <<lBallot, rBallot, rVoted, learned>>

(* Phase 2b: acceptor a votes and echoes the vote. *)
AcceptReply(a) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= rBallot[a]
        /\ rBallot' = [rBallot EXCEPT ![a] = m.bal]
        /\ rVoted' = [rVoted EXCEPT ![a][m.slot] = [bal |-> m.bal, val |-> m.val]]
        /\ Send([type |-> "AcceptReply", from |-> a, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED <<lBallot, lStatus, proposed, learned>>

(* Learning: leader r observes a quorum of votes for v in slot s. *)
Learn(r) ==
    \E s \in Slots :
        /\ lStatus[r][s] = "Accepting"
        /\ \E Q \in Quorums, v \in Values :
             /\ \A a \in Q :
                  [type |-> "AcceptReply", from |-> a, bal |-> lBallot[r],
                   slot |-> s, val |-> v] \in msgs
             /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
        /\ lStatus' = [lStatus EXCEPT ![r][s] = "Learned"]
        /\ UNCHANGED <<msgs, lBallot, rBallot, rVoted, proposed>>

Next ==
    \E r \in Replicas :
        \/ Prepare(r)
        \/ PrepareReply(r)
        \/ Accept(r)
        \/ AcceptReply(r)
        \/ Learn(r)

Spec == Init /\ [][Next]_vars

=============================================================================
---------------------------- MODULE MultiPaxos ----------------------------
(***************************************************************************)
(* Multi-Decree Paxos (Multi-Paxos) with unified replica roles and an      *)
(* aggregated prepare phase.  Every replica acts as proposer, acceptor     *)
(* and learner.  A single Phase 1 (prepare) per ballot covers all slots:   *)
(* acceptors answer with their full per-slot voting history, and the new   *)
(* leader may then run Phase 2 (accept) for any slot in that ballot.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Replicas,   \* set of replicas (each is proposer/acceptor/learner)
          Values,     \* set of proposable values
          Slots,      \* finite set of log positions
          Ballots,    \* set of ballot numbers (natural numbers)
          None        \* distinguished "no value" marker

ASSUME /\ IsFiniteSet(Replicas)
       /\ Cardinality(Replicas) >= 3
       /\ IsFiniteSet(Slots)
       /\ Ballots \subseteq Nat
       /\ None \notin Values

-----------------------------------------------------------------------------
(* Quorums: majorities of replicas.  Any two majorities intersect.         *)
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

NoBallot == -1

(* An acceptor's vote in a slot: the highest ballot and value accepted.    *)
Vote == [bal : Ballots \cup {NoBallot}, val : Values \cup {None}]

NoVote == [bal |-> NoBallot, val |-> None]

Messages ==
       [type : {"1a"}, from : Replicas, bal : Ballots]
  \cup [type : {"1b"}, from : Replicas, bal : Ballots, voted : [Slots -> Vote]]
  \cup [type : {"2a"}, from : Replicas, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, from : Replicas, bal : Ballots, slot : Slots, val : Values]

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

-----------------------------------------------------------------------------
VARIABLES maxBal,    \* maxBal[r]: highest ballot replica r has promised
          accepted,  \* accepted[r][s]: highest-ballot vote of r in slot s
          learned,   \* learned[r][s]: value r learned for slot s, or None
          msgs       \* set of all messages ever sent

vars == <<maxBal, accepted, learned, msgs>>

TypeOK ==
  /\ maxBal   \in [Replicas -> Ballots \cup {NoBallot}]
  /\ accepted \in [Replicas -> [Slots -> Vote]]
  /\ learned  \in [Replicas -> [Slots -> Values \cup {None}]]
  /\ msgs     \subseteq Messages

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
  /\ maxBal   = [r \in Replicas |-> NoBallot]
  /\ accepted = [r \in Replicas |-> [s \in Slots |-> NoVote]]
  /\ learned  = [r \in Replicas |-> [s \in Slots |-> None]]
  /\ msgs     = {}

(* Phase 1a: replica r tries to become leader with ballot b.  One prepare  *)
(* message covers all slots.                                               *)
Phase1a(r, b) ==
  /\ b > maxBal[r]
  /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b   \* ballots are unique to one leader
  /\ Send([type |-> "1a", from |-> r, bal |-> b])
  /\ UNCHANGED <<maxBal, accepted, learned>>

(* Phase 1b: acceptor r promises ballot m.bal and reports its complete     *)
(* voting history across all slots.                                        *)
Phase1b(r, m) ==
  /\ m \in msgs
  /\ m.type = "1a"
  /\ m.bal > maxBal[r]
  /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
  /\ Send([type |-> "1b", from |-> r, bal |-> m.bal, voted |-> accepted[r]])
  /\ UNCHANGED <<accepted, learned>>

(* Leader r has gathered 1b responses for ballot b from quorum Q.          *)
Is1bQuorum(b, Q) ==
  \A q \in Q : \E m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from = q

(* Value v is safe to propose in slot s at ballot b given quorum Q:        *)
(* if any member of Q reported a vote in s, v must be the value of the     *)
(* highest-ballot such vote; otherwise any value is allowed.               *)
SafeValue(b, Q, s, v) ==
  LET Q1b   == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
      votes == {m.voted[s] : m \in Q1b}
      maxb  == Max({vt.bal : vt \in votes})
  IN  \/ maxb = NoBallot
      \/ \E vt \in votes : vt.bal = maxb /\ vt.val = v

(* Phase 2a: leader r proposes value v for slot s in ballot b.  Allowed    *)
(* only once r established leadership with a majority of 1b messages, and  *)
(* at most one proposal per (ballot, slot).                                *)
Phase2a(r, b, s, v) ==
  /\ \E m \in msgs : m.type = "1a" /\ m.bal = b /\ m.from = r
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       /\ Is1bQuorum(b, Q)
       /\ SafeValue(b, Q, s, v)
  /\ Send([type |-> "2a", from |-> r, bal |-> b, slot |-> s, val |-> v])
  /\ UNCHANGED <<maxBal, accepted, learned>>

(* Phase 2b: acceptor r accepts a proposal if it has not promised a higher *)
(* ballot.                                                                 *)
Phase2b(r, m) ==
  /\ m \in msgs
  /\ m.type = "2a"
  /\ m.bal >= maxBal[r]
  /\ maxBal'   = [maxBal EXCEPT ![r] = m.bal]
  /\ accepted' = [accepted EXCEPT ![r][m.slot] = [bal |-> m.bal, val |-> m.val]]
  /\ Send([type |-> "2b", from |-> r, bal |-> m.bal, slot |-> m.slot, val |-> m.val])
  /\ UNCHANGED learned

(* Learn: replica r learns v for slot s once a majority accepted v in the  *)
(* same ballot.  A learned decision is final.                              *)
Learn(r, s, b, v) ==
  /\ learned[r][s] = None
  /\ \E Q \in Quorums :
       \A q \in Q : \E m \in msgs :
          /\ m.type = "2b" /\ m.from = q
          /\ m.bal = b /\ m.slot = s /\ m.val = v
  /\ learned' = [learned EXCEPT ![r][s] = v]
  /\ UNCHANGED <<maxBal, accepted, msgs>>

Next ==
  \/ \E r \in Replicas, b \in Ballots : Phase1a(r, b)
  \/ \E r \in Replicas, m \in msgs : Phase1b(r, m)
  \/ \E r \in Replicas, b \in Ballots, s \in Slots, v \in Values : Phase2a(r, b, s, v)
  \/ \E r \in Replicas, m \in msgs : Phase2b(r, m)
  \/ \E r \in Replicas, s \in Slots, b \in Ballots, v \in Values : Learn(r, s, b, v)

Spec == Init /\ [][Next]_vars

(* Weak fairness on the protocol; progress is not guaranteed in general    *)
(* (dueling leaders), so liveness is stated but not required to hold.      *)
FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Chosen: a majority accepted v in slot s within a single ballot.         *)
ChosenAt(s, b, v) ==
  \E Q \in Quorums :
    \A q \in Q : \E m \in msgs :
      m.type = "2b" /\ m.from = q /\ m.bal = b /\ m.slot = s /\ m.val = v

Chosen(s) == {v \in Values : \E b \in Ballots : ChosenAt(s, b, v)}

Proposed(s) == {m.val : m \in {mm \in msgs : mm.type = "2a" /\ mm.slot = s}}

(* Consensus safety: at most one value chosen per slot, and all learners   *)
(* agree.                                                                  *)
ChosenSafety == \A s \in Slots : Cardinality(Chosen(s)) <= 1

Consistency ==
  \A r1, r2 \in Replicas, s \in Slots :
    (learned[r1][s] # None /\ learned[r2][s] # None)
      => learned[r1][s] = learned[r2][s]

(* Validity: any learned value was previously proposed for that slot.      *)
Validity ==
  \A r \in Replicas, s \in Slots :
    learned[r][s] # None => learned[r][s] \in Proposed(s)

(* Learned values are actually chosen.                                     *)
LearnedChosen ==
  \A r \in Replicas, s \in Slots :
    learned[r][s] # None => learned[r][s] \in Chosen(s)

Safety == TypeOK /\ ChosenSafety /\ Consistency /\ Validity /\ LearnedChosen

(* Decisions are final.                                                    *)
LearnedStable ==
  [][\A r \in Replicas, s \in Slots :
        learned[r][s] # None => learned'[r][s] = learned[r][s]]_vars

(* Non-triviality: checking this invariant should yield a counterexample,  *)
(* demonstrating that a value can be learned.                              *)
NothingLearned == \A r \in Replicas, s \in Slots : learned[r][s] = None

(* Liveness (desired, not guaranteed under all conditions).                *)
EventuallySomethingLearned ==
  <>(\E r \in Replicas, s \in Slots : learned[r][s] # None)

THEOREM Spec => [](Safety) /\ LearnedStable
=============================================================================
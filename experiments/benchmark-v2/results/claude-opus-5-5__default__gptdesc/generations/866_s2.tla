------------------------------ MODULE FastPaxos ------------------------------
(***************************************************************************)
(* A simplified specification of Lamport's Fast Paxos consensus protocol.  *)
(*                                                                         *)
(* Simplifications:                                                        *)
(*   - A single, unique coordinator owns every ballot, so at most one      *)
(*     phase 1a and one phase 2a message is ever sent for each ballot.     *)
(*   - Failures are not modeled explicitly. Agents restore their state     *)
(*     from stable storage, and message loss or duplication is captured   *)
(*     because messages are never removed from the message set.            *)
(*   - All agents communicate directly with one another.                   *)
(*                                                                         *)
(* There are two kinds of ballots (rounds):                                *)
(*   - Classic ballots: the coordinator picks the value.                   *)
(*   - Fast ballots: if the coordinator is free to pick any value, it      *)
(*     sends a special "Any" message. Acceptors then vote directly for     *)
(*     proposed values, which can cause collisions.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Replicas,        \* The set of acceptors
          Values,          \* The set of values that may be proposed
          ClassicBallots,  \* Ballot numbers of classic rounds
          FastBallots,     \* Ballot numbers of fast rounds
          ClassicQuorums,  \* Quorums used in classic rounds and in phase 1
          FastQuorums      \* Quorums used to choose a value in fast rounds

Ballots == ClassicBallots \cup FastBallots

ASSUME BallotAssumption ==
          /\ ClassicBallots \cap FastBallots = {}
          /\ Ballots \subseteq (Nat \ {0})

ASSUME QuorumAssumption ==
          /\ ClassicQuorums \subseteq SUBSET Replicas
          /\ FastQuorums \subseteq SUBSET Replicas
          /\ ClassicQuorums # {}
          /\ FastQuorums # {}
          \* Any two classic quorums intersect.
          /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}
          \* Any classic quorum intersects any fast quorum.
          /\ \A Q \in ClassicQuorums, R \in FastQuorums : Q \cap R # {}
          \* Any classic quorum and any two fast quorums have a common member.
          /\ \A Q \in ClassicQuorums, R1, R2 \in FastQuorums :
                Q \cap R1 \cap R2 # {}

None == CHOOSE v : v \notin Values
Any  == CHOOSE v : v \notin Values \cup {None}

Quorum(b) == IF b \in FastBallots THEN FastQuorums ELSE ClassicQuorums

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Message ==
       [type : {"P1a"}, ballot : Ballots]
  \cup [type : {"P1b"}, ballot : Ballots, replica : Replicas,
        maxVBal : Ballots \cup {0}, maxVal : Values \cup {None}]
  \cup [type : {"P2a"}, ballot : Ballots, value : Values \cup {Any}]
  \cup [type : {"P2b"}, ballot : Ballots, replica : Replicas, value : Values]

VARIABLES msgs,      \* The set of all messages that have been sent
          maxBal,    \* maxBal[r]: highest ballot in which r has participated
          maxVBal,   \* maxVBal[r]: highest ballot in which r has voted
          maxVal,    \* maxVal[r]: value r voted for in ballot maxVBal[r]
          proposed,  \* The set of values that have been proposed
          learned    \* The set of values that have been learned (decided)

vars == <<msgs, maxBal, maxVBal, maxVal, proposed, learned>>

TypeOK ==
  /\ msgs \subseteq Message
  /\ maxBal \in [Replicas -> Ballots \cup {0}]
  /\ maxVBal \in [Replicas -> Ballots \cup {0}]
  /\ maxVal \in [Replicas -> Values \cup {None}]
  /\ proposed \subseteq Values
  /\ learned \subseteq Values

Init ==
  /\ msgs = {}
  /\ maxBal = [r \in Replicas |-> 0]
  /\ maxVBal = [r \in Replicas |-> 0]
  /\ maxVal = [r \in Replicas |-> None]
  /\ proposed = {}
  /\ learned = {}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* A client proposes a value.                                              *)
(***************************************************************************)
Propose(v) ==
  /\ v \notin proposed
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED <<msgs, maxBal, maxVBal, maxVal, learned>>

(***************************************************************************)
(* Phase 1a: the unique coordinator starts ballot b.                       *)
(***************************************************************************)
Phase1a(b) ==
  /\ ~\E m \in msgs : m.type = "P1a" /\ m.ballot = b
  /\ Send([type |-> "P1a", ballot |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, learned>>

(***************************************************************************)
(* Phase 1b: replica r promises to participate in ballot b.                *)
(***************************************************************************)
Phase1b(r) ==
  \E m \in msgs :
     /\ m.type = "P1a"
     /\ m.ballot > maxBal[r]
     /\ maxBal' = [maxBal EXCEPT ![r] = m.ballot]
     /\ Send([type |-> "P1b", ballot |-> m.ballot, replica |-> r,
              maxVBal |-> maxVBal[r], maxVal |-> maxVal[r]])
     /\ UNCHANGED <<maxVBal, maxVal, proposed, learned>>

(***************************************************************************)
(* The coordinator sends a phase 2a message for ballot b with value v.     *)
(***************************************************************************)
Send2a(b, v) == Send([type |-> "P2a", ballot |-> b, value |-> v])

(***************************************************************************)
(* The coordinator is free to pick any value. In a fast ballot it sends    *)
(* "Any". In a classic ballot it picks some proposed value.                *)
(***************************************************************************)
SendFree(b) ==
  IF b \in FastBallots
     THEN Send2a(b, Any)
     ELSE \E v \in proposed : Send2a(b, v)

(***************************************************************************)
(* Phase 2a: the coordinator selects a value using the P1b messages from a *)
(* classic quorum Q. Let k be the highest ballot in which some member of Q *)
(* voted.                                                                  *)
(*   - If k = 0, no value can have been chosen, so any value is safe.     *)
(*   - If k is a classic ballot, the single value voted in k is safe.     *)
(*   - If k is a fast ballot, value w may have been chosen in k only if    *)
(*     some fast quorum R exists such that every member of R \cap Q voted  *)
(*     for w in k. The quorum assumption makes such a w unique. If no      *)
(*     such w exists (for example, after a collision), any value is safe.  *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~\E m \in msgs : m.type = "P2a" /\ m.ballot = b
  /\ \E Q \in ClassicQuorums :
       LET S == {m \in msgs : /\ m.type = "P1b"
                              /\ m.ballot = b
                              /\ m.replica \in Q}
       IN  /\ \A r \in Q : \E m \in S : m.replica = r
           /\ LET k == Max({m.maxVBal : m \in S})
                  V == {m.maxVal : m \in {mm \in S : mm.maxVBal = k}}
                  O4(w) == \E R \in FastQuorums :
                              \A a \in R \cap Q :
                                 \E m \in S : /\ m.replica = a
                                              /\ m.maxVBal = k
                                              /\ m.maxVal = w
              IN  IF k = 0
                     THEN SendFree(b)
                  ELSE IF k \in ClassicBallots
                     THEN \E w \in V : Send2a(b, w)
                  ELSE IF \E w \in V : O4(w)
                     THEN \E w \in V : O4(w) /\ Send2a(b, w)
                  ELSE SendFree(b)
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, learned>>

(***************************************************************************)
(* Phase 2b: replica r votes in a ballot. If the phase 2a message is       *)
(* "Any" (fast ballot), r votes for any value that has been proposed.      *)
(***************************************************************************)
Phase2b(r) ==
  \E m \in msgs :
     /\ m.type = "P2a"
     /\ m.ballot >= maxBal[r]
     /\ maxVBal[r] < m.ballot
     /\ \E v \in (IF m.value = Any THEN proposed ELSE {m.value}) :
           /\ maxBal' = [maxBal EXCEPT ![r] = m.ballot]
           /\ maxVBal' = [maxVBal EXCEPT ![r] = m.ballot]
           /\ maxVal' = [maxVal EXCEPT ![r] = v]
           /\ Send([type |-> "P2b", ballot |-> m.ballot,
                    replica |-> r, value |-> v])
     /\ UNCHANGED <<proposed, learned>>

(***************************************************************************)
(* Value v is chosen in ballot b when a quorum of the right kind for b     *)
(* has voted for v in b.                                                   *)
(***************************************************************************)
ChosenIn(b, v) ==
  \E Q \in Quorum(b) :
     \A r \in Q :
        \E m \in msgs : /\ m.type = "P2b"
                        /\ m.ballot = b
                        /\ m.replica = r
                        /\ m.value = v

Chosen(v) == \E b \in Ballots : ChosenIn(b, v)

Learn(v) ==
  /\ Chosen(v)
  /\ learned' = learned \cup {v}
  /\ UNCHANGED <<msgs, maxBal, maxVBal, maxVal, proposed>>

Next ==
  \/ \E v \in Values : Propose(v)
  \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
  \/ \E r \in Replicas : Phase1b(r) \/ Phase2b(r)
  \/ \E v \in Values : Learn(v)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Non-triviality: only values that have been proposed can be learned.
Nontriviality == \A v \in learned : v \in proposed

\* Consistency: at most one value is learned.
Consistency == Cardinality(learned) <= 1

\* Every vote is for a proposed value.
VotesProposed ==
  \A m \in msgs : m.type = "P2b" => m.value \in proposed

Inv == TypeOK /\ Nontriviality /\ Consistency /\ VotesProposed

THEOREM Spec => [](TypeOK /\ Nontriviality)
=============================================================================
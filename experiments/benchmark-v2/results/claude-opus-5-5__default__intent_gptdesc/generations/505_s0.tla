---- MODULE SingleDecreePaxos ----
(***************************************************************************)
(* Single-decree Paxos with one fixed proposer (no leader election).        *)
(*                                                                         *)
(* Asynchronous network: `msgs` is a monotonically growing set of all      *)
(* messages ever sent. A message stays in the set once sent. As a result,  *)
(* any message may be received any number of times (duplication), at any  *)
(* later time (delay), in any order (reordering), or never (loss). Message *)
(* contents are never altered, so there is no corruption.                  *)
(*                                                                         *)
(* Ballots are a finite set of natural numbers, totally ordered by <.      *)
(* The single proposer may start Phase 1 for any ballot.                   *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Values,     \* finite nonempty set of proposable values
          Acceptors,  \* finite set of acceptors
          Quorums,    \* set of quorums (subsets of Acceptors)
          Ballots,    \* finite set of ballot numbers (subset of Nat)
          None        \* "no value" marker

ASSUME ValuesAssumption   == Values # {} /\ IsFiniteSet(Values)
ASSUME AcceptorAssumption == Acceptors # {} /\ IsFiniteSet(Acceptors)
ASSUME BallotAssumption   == Ballots # {} /\ Ballots \subseteq Nat /\ IsFiniteSet(Ballots)
ASSUME NoneAssumption     == None \notin Values
ASSUME QuorumAssumption   ==
          /\ Quorums # {}
          /\ \A Q \in Quorums : Q \subseteq Acceptors /\ Q # {}
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

NoBallot == -1   \* below every real ballot

Message ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal,   \* maxBal[a]  : highest ballot acceptor a has promised/seen
          maxVBal,  \* maxVBal[a] : highest ballot in which a accepted a value
          maxVal,   \* maxVal[a]  : value a accepted in ballot maxVBal[a]
          msgs      \* set of all messages ever sent

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
  /\ maxBal  \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxVal  \in [Acceptors -> Values \cup {None}]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal  = [a \in Acceptors |-> NoBallot]
  /\ maxVBal = [a \in Acceptors |-> NoBallot]
  /\ maxVal  = [a \in Acceptors |-> None]
  /\ msgs    = {}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Phase 1a: the fixed proposer sends a prepare for ballot b.              *)
(***************************************************************************)
Phase1a(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b: an acceptor receives a prepare with a ballot above its        *)
(* promise. It promises that ballot and replies with its last accepted     *)
(* ballot and value.                                                       *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
              mbal |-> maxVBal[a], mval |-> maxVal[a]])
     /\ UNCHANGED <<maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2a: the proposer has 1b replies for ballot b from a quorum Q and  *)
(* has not yet proposed in ballot b. It proposes v according to the Paxos  *)
(* rule:                                                                   *)
(*   - If no member of Q reported an accepted value, v may be any value.   *)
(*   - Otherwise, v is the value reported with the highest mbal.           *)
(***************************************************************************)
Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal # NoBallot}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts a proposal whose ballot is at least its   *)
(* promise.                                                                *)
(***************************************************************************)
Phase2b(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[a]
     /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

ProposerNext == \E b \in Ballots : Phase1a(b) \/ \E v \in Values : Phase2a(b, v)

Next == ProposerNext \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

(* Safety specification: arbitrary scheduling, no fairness. *)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Derived notions                                                         *)
(***************************************************************************)
VotedFor(a, b, v) == [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

chosen == {v \in Values : Chosen(v)}

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedFor(a, b, v)
                    /\ maxBal[a] > b

SafeAt(b, v) ==
  \A c \in Ballots :
     c < b => \E Q \in Quorums :
                 \A a \in Q : VotedFor(a, c, v) \/ WontVoteIn(a, c)

(***************************************************************************)
(* Safety: Agreement                                                       *)
(***************************************************************************)
Agreement == \A v, w \in chosen : v = w

AtMostOneChosen == Cardinality(chosen) <= 1

\* No two acceptors accept different values in the same ballot.
OneValuePerBallot ==
  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
     VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => v1 = v2

\* At most one proposal per ballot.
OneProposalPerBallot ==
  \A m1, m2 \in msgs :
     (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1.val = m2.val

\* No acceptance across ballots can lead to conflicting decisions.
\* A vote in ballot b for v is safe at b, so no other value is chosen below b.
VotesSafe ==
  \A a \in Acceptors, b \in Ballots, v \in Values :
     VotedFor(a, b, v) => SafeAt(b, v)

(***************************************************************************)
(* Consistency with the Paxos choice rule                                  *)
(***************************************************************************)
\* Every proposal respects the highest prior accepted ballots.
ProposalsSafe ==
  \A m \in msgs : m.type = "2a" => SafeAt(m.bal, m.val)

\* Every chosen value was proposed in that ballot under the rule.
ChosenWasProposed ==
  \A b \in Ballots, v \in Values :
     ChosenAt(b, v) =>
        /\ [type |-> "2a", bal |-> b, val |-> v] \in msgs
        /\ SafeAt(b, v)

\* A value chosen at b is the value proposed in every later ballot.
ChosenPersists ==
  \A b \in Ballots, v \in Values :
     ChosenAt(b, v) =>
        \A m \in msgs : (m.type = "2a" /\ m.bal > b) => m.val = v

(***************************************************************************)
(* Integrity                                                               *)
(***************************************************************************)
ChosenIntegrity == chosen \subseteq Values

AcceptIntegrity ==
  /\ \A m \in msgs :
        m.type = "2b" =>
           /\ [type |-> "2a", bal |-> m.bal, val |-> m.val] \in msgs
           /\ maxBal[m.acc] >= m.bal
           /\ maxVBal[m.acc] >= m.bal
  /\ \A a \in Acceptors :
        /\ maxVBal[a] <= maxBal[a]
        /\ (maxVBal[a] = NoBallot) <=> (maxVal[a] = None)
        /\ maxVBal[a] # NoBallot => VotedFor(a, maxVBal[a], maxVal[a])

PromiseIntegrity ==
  \A m \in msgs :
     m.type = "1b" =>
        /\ m.mbal < m.bal
        /\ maxBal[m.acc] >= m.bal
        /\ (m.mbal # NoBallot) => VotedFor(m.acc, m.mbal, m.mval)
        /\ (m.mbal = NoBallot) <=> (m.mval = None)

(***************************************************************************)
(* Quorum intersection (constant invariant, follows from the assumption)   *)
(***************************************************************************)
QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

THEOREM SafetyTheorem ==
  Spec => [](TypeOK /\ Agreement /\ OneValuePerBallot /\ ProposalsSafe
             /\ ChosenIntegrity /\ AcceptIntegrity /\ QuorumIntersection)

(***************************************************************************)
(* Optional liveness. This assumes no acceptor fails and the fixed         *)
(* proposer runs, with eventual delivery. Eventual delivery is modeled as  *)
(* weak fairness of the receive actions on the persistent message set.     *)
(* Because Ballots is finite, the highest ballot is eventually prepared    *)
(* and cannot be preempted, so a value is eventually chosen.               *)
(***************************************************************************)
FairSpec ==
  /\ Spec
  /\ WF_vars(\E b \in Ballots : Phase1a(b))
  /\ WF_vars(\E b \in Ballots, v \in Values : Phase2a(b, v))
  /\ \A a \in Acceptors : WF_vars(Phase1b(a)) /\ WF_vars(Phase2b(a))

Liveness == <>(chosen # {})

StableDecision == \A v \in Values : [](Chosen(v) => []Chosen(v))

THEOREM LivenessTheorem == FairSpec => Liveness
====
------------------------------- MODULE Paxos -------------------------------

EXTENDS Naturals, FiniteSets

(*
  Classic Paxos over four replicas with 3-of-4 quorums.
  Replicas act as both proposers and acceptors.
*)

(***************************************************************************)
(* Basic sets and constants                                                *)
(***************************************************************************)

Replicas == 1..4

BMax == 5
Ballots == 0..BMax
NonzeroBallots == Ballots \ {0}

Values == {"v1", "v2", "v3"}

None == "None"

Quorums == { Q \in SUBSET Replicas : Cardinality(Q) = 3 }

(***************************************************************************)
(* Message vocabulary                                                      *)
(***************************************************************************)

MessageSet ==
  { [type |-> "1a", from |-> p, to |-> a, ballot |-> b]
    : p \in Replicas, a \in Replicas, b \in NonzeroBallots } \cup
  { [type |-> "1b", from |-> a, to |-> p, ballot |-> b,
      maxVBallot |-> vb, maxValue |-> v]
    : a \in Replicas, p \in Replicas, b \in NonzeroBallots,
      vb \in Ballots, v \in (Values \cup {None}) } \cup
  { [type |-> "2a", from |-> p, to |-> a, ballot |-> b, value |-> v]
    : p \in Replicas, a \in Replicas, b \in NonzeroBallots, v \in Values } \cup
  { [type |-> "2b", from |-> a, to |-> p, ballot |-> b, value |-> v]
    : a \in Replicas, p \in Replicas, b \in NonzeroBallots, v \in Values }

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  messages,      \* set of messages in the system
  maxBallot,     \* [a \in Replicas -> Ballots], highest promised ballot
  maxVBallot,    \* [a \in Replicas -> Ballots], highest accepted ballot
  maxValue,      \* [a \in Replicas -> Values \cup {None}], value at maxVBallot
  decision       \* learned decision (a single value), or None

vars == << messages, maxBallot, maxVBallot, maxValue, decision >>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

ForcedValue(S) ==
  LET T == { m \in S : m.maxVBallot # 0 } IN
    IF T = {} THEN None
    ELSE
      LET VBs == { m.maxVBallot : m \in T } IN
      LET mx  == CHOOSE vb \in VBs : \A u \in VBs : vb >= u IN
      (CHOOSE m \in T : m.maxVBallot = mx).maxValue

ProposedValues(messages_) ==
  { m.value : m \in messages_ /\ m.type = "2a" }

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ messages = {}
  /\ maxBallot = [a \in Replicas |-> 0]
  /\ maxVBallot = [a \in Replicas |-> 0]
  /\ maxValue = [a \in Replicas |-> None]
  /\ decision = None

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

PaxosPrepare ==
  \E p \in Replicas, b \in NonzeroBallots :
    /\ messages' = messages \cup { [type |-> "1a", from |-> p, to |-> a, ballot |-> b] : a \in Replicas }
    /\ UNCHANGED << maxBallot, maxVBallot, maxValue, decision >>

PaxosPromise ==
  \E a \in Replicas, p \in Replicas, b \in NonzeroBallots :
    /\ [type |-> "1a", from |-> p, to |-> a, ballot |-> b] \in messages
    /\ b > maxBallot[a]
    /\ messages' = messages \cup {
         [ type |-> "1b", from |-> a, to |-> p, ballot |-> b,
           maxVBallot |-> maxVBallot[a], maxValue |-> maxValue[a] ] }
    /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
    /\ UNCHANGED << maxVBallot, maxValue, decision >>

PaxosAccept ==
  \E p \in Replicas, b \in NonzeroBallots, Q \in Quorums :
    /\ \A a \in Q :
         \E m \in messages :
           /\ m.type = "1b"
           /\ m.to = p
           /\ m.ballot = b
           /\ m.from = a
    /\ LET S == { m \in messages :
                    /\ m.type = "1b"
                    /\ m.to = p
                    /\ m.ballot = b
                    /\ m.from \in Q } IN
       LET fv == ForcedValue(S) IN
       \E v \in (IF fv = None THEN Values ELSE {fv}) :
         /\ messages' = messages \cup {
               [type |-> "2a", from |-> p, to |-> a, ballot |-> b, value |-> v] : a \in Replicas }
         /\ UNCHANGED << maxBallot, maxVBallot, maxValue, decision >>

PaxosAccepted ==
  \E a \in Replicas, p \in Replicas, b \in NonzeroBallots, v \in Values :
    /\ [type |-> "2a", from |-> p, to |-> a, ballot |-> b, value |-> v] \in messages
    /\ b >= maxBallot[a]
    /\ messages' = messages \cup {
         [type |-> "2b", from |-> a, to |-> p, ballot |-> b, value |-> v] }
    /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
    /\ maxVBallot' = [maxVBallot EXCEPT ![a] = b]
    /\ maxValue' = [maxValue EXCEPT ![a] = v]
    /\ UNCHANGED decision

PaxosDecide ==
  \E b \in NonzeroBallots, v \in Values, Q \in Quorums :
    /\ decision = None
    /\ \A a \in Q :
         \E m \in messages :
           /\ m.type = "2b"
           /\ m.ballot = b
           /\ m.value = v
           /\ m.from = a
    /\ decision' = v
    /\ UNCHANGED << messages, maxBallot, maxVBallot, maxValue >>

Next ==
  PaxosPrepare \/ PaxosPromise \/ PaxosAccept \/ PaxosAccepted \/ PaxosDecide

(***************************************************************************)
(* Type correctness, safety, and temporal spec                             *)
(***************************************************************************)

PaxosTypeOK ==
  /\ messages \subseteq MessageSet
  /\ maxBallot \in [Replicas -> Ballots]
  /\ maxVBallot \in [Replicas -> Ballots]
  /\ maxValue \in [Replicas -> (Values \cup {None})]
  /\ decision \in (Values \cup {None})
  /\ \A a \in Replicas : (maxVBallot[a] = 0) <=> (maxValue[a] = None)

PaxosNontriviality ==
  [](decision = None \/ decision \in ProposedValues(messages))

PaxosConsistency ==
  [](decision = None \/ decision' = decision)

PaxosSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(PaxosDecide)

=============================================================================
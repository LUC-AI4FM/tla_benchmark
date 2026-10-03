---- MODULE FastPaxos ----
EXTENDS Integers, FiniteSets

(*
  A simplified Fast Paxos specification with a unique coordinator and direct communication.
  We model one fast round (0) and one classic round (1). Failures are not modeled explicitly.
  Quorums:
    - Classic quorums are any subsets of acceptors of size >= 2.
    - Fast quorums are the full set of acceptors.
  Decisions (Chosen) occur when a quorum of acceptors have accepted the same value in a round.
*)

CONSTANT NoVal \* distinguished non-value

(***************************************************************************)
(* Basic sets                                                              *)
(***************************************************************************)
VALUES     == {"v1", "v2"}
PROPOSERS  == {"p1", "p2"}
ACCEPTORS  == {"a1", "a2", "a3"}

ROUNDS     == {0, 1} \* 0 = fast round, 1 = classic round

ClassicQuorums == { Q \in SUBSET ACCEPTORS : Cardinality(Q) >= 2 }
FastQuorums    == { ACCEPTORS }

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES proposals,    \* set of proposed values
          maxBal,       \* [a -> highest round promised (prepared)]
          maxVBal,      \* [a -> highest round in which a accepted some value]
          maxVal        \* [a -> the value accepted at maxVBal, or NoVal if none]

vars == << proposals, maxBal, maxVBal, maxVal >>

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ proposals = {}
  /\ maxBal = [a \in ACCEPTORS |-> -1]
  /\ maxVBal = [a \in ACCEPTORS |-> -1]
  /\ maxVal = [a \in ACCEPTORS |-> NoVal]

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
FastTypeOK ==
  /\ proposals \subseteq VALUES
  /\ maxBal \in [ACCEPTORS -> (ROUNDS \cup {-1})]
  /\ maxVBal \in [ACCEPTORS -> (ROUNDS \cup {-1})]
  /\ maxVal \in [ACCEPTORS -> (VALUES \cup {NoVal})]
  /\ \A a \in ACCEPTORS : (maxVBal[a] = -1) <=> (maxVal[a] = NoVal)
  /\ \A a \in ACCEPTORS : (maxVBal[a] = -1) \/ (maxBal[a] >= maxVBal[a])

(***************************************************************************)
(* Helper predicates: chosen values                                        *)
(***************************************************************************)
FastChosen(v) ==
  \E F \in FastQuorums :
    \A a \in F : (maxVBal[a] = 0) /\ (maxVal[a] = v)

ClassicChosen(v) ==
  \E Q \in ClassicQuorums :
    \A a \in Q : (maxVBal[a] = 1) /\ (maxVal[a] = v)

Chosen(v) == FastChosen(v) \/ ClassicChosen(v)

(***************************************************************************)
(* Safe value selection for the classic round (collision handling)         *)
(***************************************************************************)
SafeClassic ==
  IF \E v \in VALUES : FastChosen(v) THEN { v \in VALUES : FastChosen(v) }
  ELSE IF \E v \in VALUES : ClassicChosen(v) THEN { v \in VALUES : ClassicChosen(v) }
  ELSE proposals

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Propose(p, v) ==
  /\ p \in PROPOSERS
  /\ v \in VALUES
  /\ proposals' = proposals \cup {v}
  /\ UNCHANGED << maxBal, maxVBal, maxVal >>

AcceptFast(a, v) ==
  /\ a \in ACCEPTORS
  /\ v \in proposals
  /\ maxBal[a] <= 0
  /\ maxBal'  = [maxBal EXCEPT ![a] = 0]
  /\ maxVBal' = [maxVBal EXCEPT ![a] = 0]
  /\ maxVal'  = [maxVal EXCEPT ![a] = v]
  /\ UNCHANGED proposals

AcceptClassic(Q, v) ==
  /\ Q \in ClassicQuorums
  /\ v \in VALUES
  /\ v \in SafeClassic
  /\ \A a \in Q : maxBal[a] <= 1
  /\ \A a \in Q : (maxVBal[a] = -1) \/ (maxVBal[a] = 0) \/ (maxVBal[a] = 1 /\ maxVal[a] = v)
  /\ maxBal'  = [a \in ACCEPTORS |-> IF a \in Q THEN 1 ELSE maxBal[a]]
  /\ maxVBal' = [a \in ACCEPTORS |-> IF a \in Q THEN 1 ELSE maxVBal[a]]
  /\ maxVal'  = [a \in ACCEPTORS |-> IF a \in Q THEN v ELSE maxVal[a]]
  /\ UNCHANGED proposals

Next ==
  \/ \E p \in PROPOSERS, v \in VALUES : Propose(p, v)
  \/ \E a \in ACCEPTORS, v \in VALUES : AcceptFast(a, v)
  \/ \E Q \in ClassicQuorums, v \in VALUES : AcceptClassic(Q, v)

(***************************************************************************)
(* Behavior specification                                                  *)
(***************************************************************************)
FastSpec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
FastNontriviality ==
  \A v \in VALUES : Chosen(v) => v \in proposals

PaxosConsistency ==
  \A u \in VALUES : \A v \in VALUES : (Chosen(u) /\ Chosen(v)) => u = v

====
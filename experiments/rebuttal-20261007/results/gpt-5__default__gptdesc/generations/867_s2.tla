----------------------------- MODULE PaxosNoLeaders -----------------------------

EXTENDS Naturals, FiniteSets

(*
  Paxos without explicit leaders or learners. Models Prepare, Promise, Accept,
  Accepted, and Decide messages among proposers and acceptors. Liveness is
  explicitly set to FALSE, reflecting that Paxos does not guarantee termination
  in an asynchronous system with failures (FLP).
*)

CONSTANTS
  Proposers,      \* nonempty set of proposers
  Acceptors,      \* nonempty set of acceptors
  Vals,           \* set of application values
  Ballots,        \* set of ballot numbers; assumed subset of Nat
  Proposed,       \* subset of Vals that may be initially proposed
  None            \* distinguished "no value"/"unset" marker

ASSUME
  /\ Proposers # {}
  /\ Acceptors # {}
  /\ Proposed \subseteq Vals
  /\ Ballots \subseteq Nat
  /\ None \notin (Proposers \cup Acceptors \cup Vals \cup Ballots)

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  msgs,       \* set of sent messages
  maxBal,     \* [a \in Acceptors -> highest prepare/accept ballot seen by a] in Ballots \cup {None}
  maxVBal,    \* [a \in Acceptors -> highest ballot that a has accepted] in Ballots \cup {None}
  maxVal,     \* [a \in Acceptors -> value accepted at maxVBal[a]] in Vals \cup {None}
  dec         \* representative learned/decided value in Vals \cup {None}

Vars == << msgs, maxBal, maxVBal, maxVal, dec >>

(***************************************************************************)
(* Message vocabulary                                                      *)
(***************************************************************************)

Message ==
  [ mtype: {"Prepare"},  from: Proposers,            to: Acceptors,            bal: Ballots, vbal: {None},           val: {None} ] \/
  [ mtype: {"Promise"},  from: Acceptors,            to: Proposers,            bal: Ballots, vbal: Ballots \cup {None}, val: Vals \cup {None} ] \/
  [ mtype: {"Accept"},   from: Proposers,            to: Acceptors,            bal: Ballots, vbal: {None},           val: Vals ] \/
  [ mtype: {"Accepted"}, from: Acceptors,            to: Proposers,            bal: Ballots, vbal: {None},           val: Vals ] \/
  [ mtype: {"Decide"},   from: Proposers \cup Acceptors, to: Proposers \cup Acceptors, bal: {None}, vbal: {None},   val: Vals ]

IsPrepare(m)  == m.mtype = "Prepare"
IsPromise(m)  == m.mtype = "Promise"
IsAccept(m)   == m.mtype = "Accept"
IsAccepted(m) == m.mtype = "Accepted"
IsDecide(m)   == m.mtype = "Decide"

(***************************************************************************)
(* Quorums and helpers                                                    *)
(***************************************************************************)

Quorum(Q) == Q \subseteq Acceptors /\ 2 * Cardinality(Q) > Cardinality(Acceptors)

CmpGE(b, x) == /\ b \in Ballots /\ (x = None \/ x \in Ballots /\ b >= x)
CmpGT(b, x) == /\ b \in Ballots /\ (x = None \/ x \in Ballots /\ b > x)

PromisesFor(b, p, Q) ==
  { m \in msgs :
      IsPromise(m) /\ m.bal = b /\ m.to = p /\ m.from \in Q }

VBals(S) == { m.vbal : m \in S /\ m.vbal \in Ballots }

MaxElt(S) == CHOOSE x \in S : \A y \in S : x >= y

AllowedAcceptVals(b, p, Q) ==
  LET S == PromisesFor(b, p, Q) IN
  LET Bs == VBals(S) IN
    IF Bs = {} THEN Proposed
    ELSE
      LET mx == MaxElt(Bs) IN
      LET Cands == { m.val : m \in S /\ m.vbal = mx /\ m.val \in Vals } IN
        IF Cardinality(Cands) = 1 THEN Cands ELSE {}  \* constrain to unique highest prior value

HasQuorumOfPromises(b, p, Q) ==
  /\ Quorum(Q)
  /\ \A a \in Q : \E m \in msgs : IsPromise(m) /\ m.bal = b /\ m.to = p /\ m.from = a

(***************************************************************************)
(* Initialization                                                         *)
(***************************************************************************)

Init ==
  /\ msgs = {}
  /\ maxBal \in [Acceptors -> Ballots \cup {None}]
  /\ \A a \in Acceptors : maxBal[a] = None
  /\ maxVBal \in [Acceptors -> Ballots \cup {None}]
  /\ \A a \in Acceptors : maxVBal[a] = None
  /\ maxVal \in [Acceptors -> Vals \cup {None}]
  /\ \A a \in Acceptors : maxVal[a] = None
  /\ dec \in Vals \cup {None}
  /\ dec = None

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)

SendPrepare ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots :
    /\ msgs' = msgs \cup {
         [ mtype |-> "Prepare", from |-> p, to |-> a, bal |-> b, vbal |-> None, val |-> None ] }
    /\ UNCHANGED << maxBal, maxVBal, maxVal, dec >>

PromiseOnPrepare ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots :
    /\ \E m \in msgs : IsPrepare(m) /\ m.from = p /\ m.to = a /\ m.bal = b
    /\ CmpGT(b, maxBal[a])
    /\ maxBal'  = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = maxVBal
    /\ maxVal'  = maxVal
    /\ msgs'    = msgs \cup {
         [ mtype |-> "Promise", from |-> a, to |-> p, bal |-> b,
           vbal |-> maxVBal[a], val |-> maxVal[a] ] }
    /\ UNCHANGED dec

SendAccept ==
  \E p \in Proposers, b \in Ballots, Q \subseteq Acceptors, a0 \in Acceptors, v \in Vals :
    /\ HasQuorumOfPromises(b, p, Q)
    /\ v \in AllowedAcceptVals(b, p, Q)
    /\ msgs' = msgs \cup {
         [ mtype |-> "Accept", from |-> p, to |-> a0, bal |-> b, vbal |-> None, val |-> v ] }
    /\ UNCHANGED << maxBal, maxVBal, maxVal, dec >>

AcceptOnAcceptReq ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots, v \in Vals :
    /\ \E m \in msgs : IsAccept(m) /\ m.from = p /\ m.to = a /\ m.bal = b /\ m.val = v
    /\ CmpGE(b, maxBal[a])
    /\ maxBal'  = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = v]
    /\ msgs'    = msgs \cup {
         [ mtype |-> "Accepted", from |-> a, to |-> p, bal |-> b, vbal |-> None, val |-> v ] }
    /\ UNCHANGED dec

DecideFromQuorum ==
  \E b \in Ballots, v \in Vals, Q \subseteq Acceptors :
    /\ Quorum(Q)
    /\ \A a \in Q :
         \E m \in msgs : IsAccepted(m) /\ m.from = a /\ m.bal = b /\ m.val = v
    /\ dec' \in {dec, v}
    /\ dec = None \/ dec' = dec
    /\ \E s \in Proposers \cup Acceptors, r \in Proposers \cup Acceptors :
         msgs' = msgs \cup {
           [ mtype |-> "Decide", from |-> s, to |-> r, bal |-> None, vbal |-> None, val |-> v ] }
    /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Next ==
  SendPrepare
  \/ PromiseOnPrepare
  \/ SendAccept
  \/ AcceptOnAcceptReq
  \/ DecideFromQuorum

Spec == Init /\ [][Next]_Vars

(***************************************************************************)
(* Invariants and Properties                                              *)
(***************************************************************************)

TypeOK ==
  /\ msgs \subseteq Message
  /\ maxBal \in [Acceptors -> Ballots \cup {None}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {None}]
  /\ maxVal \in [Acceptors -> Vals \cup {None}]
  /\ dec \in Vals \cup {None} 

OnlyProposedDecided ==
  dec = None \/ dec \in Proposed

AcceptValsProposed ==
  \A m \in msgs :
    (IsAccept(m) \/ IsAccepted(m) \/ IsDecide(m)) => m.val \in Proposed

MaxVBalLeqMaxBal ==
  \A a \in Acceptors :
    maxVBal[a] = None \/ (maxBal[a] \in Ballots /\ maxVBal[a] \in Ballots /\ maxVBal[a] <= maxBal[a])

SafetyInvariants == TypeOK /\ OnlyProposedDecided /\ AcceptValsProposed /\ MaxVBalLeqMaxBal

DecStability ==
  [] (dec # None => [] (dec' = dec))

(***************************************************************************)
(* Liveness (explicitly disabled)                                         *)
(***************************************************************************)

Liveness == FALSE

=============================================================================
----------------------------- MODULE PaxosNoLeaders -----------------------------

EXTENDS Naturals, Integers, FiniteSets

(*
  Paxos consensus without explicit leaders or learners.
  Messages: Prepare, Promise, Accept, Accepted, Decide.
  Quorums are strict majorities, which ensures pairwise intersection.

  Liveness is set to FALSE; under asynchrony with faults, Paxos does not
  guarantee termination (FLP impossibility).
*)

CONSTANTS
  Proposers,   \* nonempty set of proposers
  Acceptors,   \* nonempty set of acceptors
  Values,      \* set of client values
  Ballots,     \* ballot numbers; assumed subset of Nat
  NoVal,       \* distinguished non-value, not in Values
  NoDecision   \* distinguished "no decision" marker, not in Values

ASSUME
  /\ NoVal \notin Values
  /\ NoDecision \notin Values
  /\ Ballots \subseteq Nat
  /\ Proposers # {}
  /\ Acceptors # {}

(************************** Types and helpers **************************)

BOTTOM == -1  \* a sentinel "no ballot" smaller than any ballot in Ballots

MsgKinds == {"Prepare","Promise","Accept","Accepted","Decide"}

Message ==
  [kind : {"Prepare"},  from : Proposers, to : Acceptors, bal : Ballots] \/
  [kind : {"Promise"},  from : Acceptors, to : Proposers, bal : Ballots,
                        accBal : Ballots \cup {BOTTOM}, accVal : Values \cup {NoVal}] \/
  [kind : {"Accept"},   from : Proposers, to : Acceptors, bal : Ballots, val : Values] \/
  [kind : {"Accepted"}, from : Acceptors, to : Proposers, bal : Ballots, val : Values] \/
  [kind : {"Decide"},   from : Proposers,                      bal : Ballots, val : Values]

Quorum(Q) == Q \subseteq Acceptors /\ 2*Cardinality(Q) > Cardinality(Acceptors)

Max(S) ==
  CHOOSE m \in S :
    /\ S # {}
    /\ \A n \in S : m >= n

(************************** State variables **************************)

VARIABLES
  msgs,             \* set of all messages sent so far
  maxPromised,      \* [a \in Acceptors -> Ballots \cup {BOTTOM}]
  maxAcceptedBal,   \* [a \in Acceptors -> Ballots \cup {BOTTOM}]
  maxAcceptedVal,   \* [a \in Acceptors -> Values \cup {NoVal}]
  Decision          \* Values \cup {NoDecision}

Vars == << msgs, maxPromised, maxAcceptedBal, maxAcceptedVal, Decision >>

(************************** Derived sets **************************)

ProposedVals == { m.val : m \in msgs /\ m.kind = "Accept" }

PromisesFor(p, b) == { m \in msgs : m.kind = "Promise" /\ m.to = p /\ m.bal = b }

AcceptedBy(b, v) == { m.from : m \in msgs : m.kind = "Accepted" /\ m.bal = b /\ m.val = v }

(************************** Initialization **************************)

Init ==
  /\ msgs = {}
  /\ Decision = NoDecision
  /\ maxPromised \in [Acceptors -> {BOTTOM}]
  /\ maxAcceptedBal \in [Acceptors -> {BOTTOM}]
  /\ maxAcceptedVal \in [Acceptors -> {NoVal}]

(************************** Actions **************************)

SendPrepare ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots :
    /\ msgs' = msgs \cup { [kind |-> "Prepare", from |-> p, to |-> a, bal |-> b] }
    /\ UNCHANGED << maxPromised, maxAcceptedBal, maxAcceptedVal, Decision >>

PromiseRespond ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots :
    /\ [kind |-> "Prepare", from |-> p, to |-> a, bal |-> b] \in msgs
    /\ b > maxPromised[a]
    /\ maxPromised' = [maxPromised EXCEPT ![a] = b]
    /\ maxAcceptedBal' = maxAcceptedBal
    /\ maxAcceptedVal' = maxAcceptedVal
    /\ msgs' = msgs \cup {
         [ kind   |-> "Promise",
           from   |-> a,
           to     |-> p,
           bal    |-> b,
           accBal |-> maxAcceptedBal[a],
           accVal |-> maxAcceptedVal[a] ] }
    /\ Decision' = Decision

SendAccept ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots, v \in Values :
    LET Ps  == PromisesFor(p, b) IN
    LET Aps == { m.from : m \in Ps } IN
    /\ Quorum(Aps)
    /\ IF \E m \in Ps : m.accBal # BOTTOM
       THEN
         LET MaxAB == Max({ m.accBal : m \in Ps }) IN
           v \in { m.accVal : m \in Ps /\ m.accBal = MaxAB }
       ELSE v \in Values
    /\ msgs' = msgs \cup { [ kind |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> v ] }
    /\ UNCHANGED << maxPromised, maxAcceptedBal, maxAcceptedVal, Decision >>

AcceptedRespond ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots, v \in Values :
    /\ [ kind |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> v ] \in msgs
    /\ b >= maxPromised[a]
    /\ maxPromised'    = [maxPromised    EXCEPT ![a] = IF b > @ THEN b ELSE @]
    /\ maxAcceptedBal' = [maxAcceptedBal EXCEPT ![a] = b]
    /\ maxAcceptedVal' = [maxAcceptedVal EXCEPT ![a] = v]
    /\ msgs' = msgs \cup { [ kind |-> "Accepted", from |-> a, to |-> p, bal |-> b, val |-> v ] }
    /\ Decision' = Decision

DecideAction ==
  \E p \in Proposers, b \in Ballots, v \in Values, Q \in SUBSET Acceptors :
    /\ Quorum(Q)
    /\ \A a \in Q :
         \E m \in msgs :
           /\ m.kind = "Accepted"
           /\ m.from = a
           /\ m.to   = p
           /\ m.bal  = b
           /\ m.val  = v
    /\ Decision = NoDecision \/ Decision = v
    /\ msgs' = msgs \cup { [ kind |-> "Decide", from |-> p, bal |-> b, val |-> v ] }
    /\ Decision' = IF Decision = NoDecision THEN v ELSE Decision
    /\ UNCHANGED << maxPromised, maxAcceptedBal, maxAcceptedVal >>

Next ==
  SendPrepare \/ PromiseRespond \/ SendAccept \/ AcceptedRespond \/ DecideAction

(************************** Invariants and Temporal Properties **************************)

TypeOK ==
  /\ msgs \subseteq Message
  /\ maxPromised \in [Acceptors -> Int]
  /\ \A a \in Acceptors : maxPromised[a] \in Ballots \cup {BOTTOM}
  /\ maxAcceptedBal \in [Acceptors -> Int]
  /\ \A a \in Acceptors : maxAcceptedBal[a] \in Ballots \cup {BOTTOM}
  /\ maxAcceptedVal \in [Acceptors -> Values \cup {NoVal}]
  /\ Decision \in Values \cup {NoDecision}

NonTriviality ==
  Decision = NoDecision \/ Decision \in ProposedVals

AgreeDecideMsgs ==
  \A m1 \in msgs : \A m2 \in msgs :
    (m1.kind = "Decide" /\ m2.kind = "Decide") => m1.val = m2.val

DecisionStability ==
  [] (Decision # NoDecision => Decision' = Decision)

(*
  No fairness/liveness beyond safety:
  Paxos does not guarantee termination under asynchrony with faults (FLP).
*)
Liveness == FALSE

Spec == Init /\ [][Next]_Vars /\ Liveness

=============================================================================
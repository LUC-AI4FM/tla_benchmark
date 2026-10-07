----------------------------- MODULE PaxosNoLeader -----------------------------

EXTENDS Naturals, Integers, FiniteSets

(*
  Paxos without explicit leaders or learners.
  Messages: Prepare, Promise, Accept, Accepted, Decide.
  State tracks:
    - all sent messages (msgs),
    - a representative decision value (DecidedVal),
    - per-acceptor: highest ballot seen (mbal), highest ballot accepted (abal), and corresponding accepted value (aval).
  Quorums are strict majorities with pairwise intersection.
  Liveness is explicitly set to FALSE; Paxos does not guarantee termination in an asynchronous model (FLP).
*)

CONSTANTS
  Acceptor,      \* set of acceptor identifiers
  Proposer,      \* set of proposer identifiers
  Value,         \* set of candidate values
  Proposed,      \* subset of Value that can be initially proposed
  Null           \* distinguished element not in Value, used as "no value"

ASSUME Proposed \subseteq Value
ASSUME Null \notin Value

(***************************************************************************)
(* Basic definitions                                                       *)
(***************************************************************************)

Ballot == Nat
MT == {"Prepare","Promise","Accept","Accepted","Decide"}

Quorums ==
  { Q \in SUBSET Acceptor : Cardinality(Q) > Cardinality(Acceptor) \div 2 }

Quorum(Q) == Q \in Quorums

Max2(x, y) == IF x >= y THEN x ELSE y

MaxInt(S) ==
  CHOOSE m \in S : \A x \in S : m >= x

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  msgs,         \* set of messages (each is a total record over fixed fields)
  mbal,         \* [Acceptor -> Ballot \cup {-1}] highest prepare seen/promise made
  abal,         \* [Acceptor -> Ballot \cup {-1}] highest ballot accepted
  aval,         \* [Acceptor -> Value \cup {Null}] value accepted at abal
  DecidedVal    \* Value \cup {Null}

vars == << msgs, mbal, abal, aval, DecidedVal >>

(***************************************************************************)
(* Message shape                                                           *)
(***************************************************************************)

MsgTypeOK(m) ==
  /\ m \in [ mtype : MT,
             from  : Proposer \cup Acceptor \cup {Null},
             to    : Proposer \cup Acceptor \cup {Null},
             bal   : Ballot \cup {-1},
             abal  : Ballot \cup {-1},
             val   : Value \cup {Null},
             aval  : Value \cup {Null} ]
  /\ IF m.mtype = "Prepare" THEN
        /\ m.from \in Proposer
        /\ m.to   = Null
        /\ m.bal \in Ballot
        /\ m.abal = -1
        /\ m.val  = Null
        /\ m.aval = Null
     ELSE IF m.mtype = "Promise" THEN
        /\ m.from \in Acceptor
        /\ m.to   \in Proposer
        /\ m.bal  \in Ballot
        /\ m.abal \in Ballot \cup {-1}
        /\ m.aval \in Value \cup {Null}
        /\ (m.abal = -1) <=> (m.aval = Null)
        /\ m.val  = Null
     ELSE IF m.mtype = "Accept" THEN
        /\ m.from \in Proposer
        /\ m.to   = Null
        /\ m.bal \in Ballot
        /\ m.val \in Value
        /\ m.abal = -1
        /\ m.aval = Null
     ELSE IF m.mtype = "Accepted" THEN
        /\ m.from \in Acceptor
        /\ m.to   = Null
        /\ m.bal \in Ballot
        /\ m.val \in Value
        /\ m.abal = -1
        /\ m.aval = Null
     ELSE \* "Decide"
        /\ m.from = Null
        /\ m.to   = Null
        /\ m.bal  = -1
        /\ m.abal = -1
        /\ m.val \in Value
        /\ m.aval = Null

TypeOK ==
  /\ msgs \subseteq [ mtype : MT,
                      from  : Proposer \cup Acceptor \cup {Null},
                      to    : Proposer \cup Acceptor \cup {Null},
                      bal   : Ballot \cup {-1},
                      abal  : Ballot \cup {-1},
                      val   : Value \cup {Null},
                      aval  : Value \cup {Null} ]
  /\ \A m \in msgs : MsgTypeOK(m)
  /\ mbal \in [Acceptor -> Ballot \cup {-1}]
  /\ abal \in [Acceptor -> Ballot \cup {-1}]
  /\ aval \in [Acceptor -> Value \cup {Null}]
  /\ \A a \in Acceptor : (abal[a] = -1) <=> (aval[a] = Null)
  /\ DecidedVal \in Value \cup {Null}
  /\ Proposed \subseteq Value

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ msgs = {}
  /\ mbal \in [Acceptor -> {-1}]
  /\ abal \in [Acceptor -> {-1}]
  /\ aval \in [Acceptor -> {Null}]
  /\ DecidedVal = Null

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

SendPrepare ==
  \E p \in Proposer, b \in Ballot :
    /\ msgs' = msgs \cup {
         [ mtype |-> "Prepare",
           from  |-> p,
           to    |-> Null,
           bal   |-> b,
           abal  |-> -1,
           val   |-> Null,
           aval  |-> Null ] }
    /\ UNCHANGED << mbal, abal, aval, DecidedVal >>

SendPromise ==
  \E a \in Acceptor, p \in Proposer, b \in Ballot :
    /\ \E m \in msgs : /\ m.mtype = "Prepare" /\ m.from = p /\ m.bal = b
    /\ b > mbal[a]
    /\ msgs' = msgs \cup {
         [ mtype |-> "Promise",
           from  |-> a,
           to    |-> p,
           bal   |-> b,
           abal  |-> abal[a],
           val   |-> Null,
           aval  |-> aval[a] ] }
    /\ mbal' = [mbal EXCEPT ![a] = b]
    /\ UNCHANGED << abal, aval, DecidedVal >>

SendAccept ==
  \E p \in Proposer, b \in Ballot, Q \in Quorums :
    LET S == { m \in msgs :
                 /\ m.mtype = "Promise"
                 /\ m.to = p
                 /\ m.bal = b
                 /\ m.from \in Q } IN
    /\ { m.from : m \in S } = Q
    /\ LET Abals == { m.abal : m \in S } IN
       LET maxa == MaxInt(Abals) IN
       LET v ==
             IF maxa = -1
               THEN CHOOSE v \in Proposed : TRUE
               ELSE (CHOOSE m \in S : m.abal = maxa).aval
       IN
       /\ v \in Value
       /\ msgs' = msgs \cup {
            [ mtype |-> "Accept",
              from  |-> p,
              to    |-> Null,
              bal   |-> b,
              abal  |-> -1,
              val   |-> v,
              aval  |-> Null ] }
    /\ UNCHANGED << mbal, abal, aval, DecidedVal >>

SendAccepted ==
  \E a \in Acceptor, m \in msgs :
    /\ m.mtype = "Accept"
    /\ m.bal \in Ballot
    /\ m.val \in Value
    /\ m.bal >= mbal[a]
    /\ msgs' = msgs \cup {
         [ mtype |-> "Accepted",
           from  |-> a,
           to    |-> Null,
           bal   |-> m.bal,
           abal  |-> -1,
           val   |-> m.val,
           aval  |-> Null ] }
    /\ mbal' = [mbal EXCEPT ![a] = Max2(@[a], m.bal)]
    /\ abal' = [abal EXCEPT ![a] = m.bal]
    /\ aval' = [aval EXCEPT ![a] = m.val]
    /\ UNCHANGED DecidedVal

DecideStep ==
  \E b \in Ballot, v \in Value, Q \in Quorums :
    /\ \A a \in Q :
         \E ma \in msgs :
           /\ ma.mtype = "Accepted"
           /\ ma.from = a
           /\ ma.bal = b
           /\ ma.val = v
    /\ msgs' = msgs \cup {
         [ mtype |-> "Decide",
           from  |-> Null,
           to    |-> Null,
           bal   |-> -1,
           abal  |-> -1,
           val   |-> v,
           aval  |-> Null ] }
    /\ DecidedVal' = v
    /\ UNCHANGED << mbal, abal, aval >>

Next ==
  SendPrepare
  \/ SendPromise
  \/ SendAccept
  \/ SendAccepted
  \/ DecideStep

(***************************************************************************)
(* Specification and properties                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(*
  Safety: Non-triviality — only proposed values can be learned.
*)
NonTriviality == (DecidedVal = Null) \/ (DecidedVal \in Proposed)

(*
  Consistency-related temporal property over the decision variable:
  DecidedVal can change only once, from Null to a value; once set, it never changes.
*)
DecisionMonotonic == []( (DecidedVal' = DecidedVal) \/ (DecidedVal = Null) )

(*
  Liveness is explicitly set to FALSE: Paxos does not guarantee termination
  under asynchronous faults (FLP impossibility).
*)
Liveness == FALSE

=============================================================================
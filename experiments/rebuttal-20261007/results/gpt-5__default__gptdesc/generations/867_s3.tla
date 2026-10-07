------------------------------- MODULE Paxos -------------------------------

EXTENDS Naturals, FiniteSets, TLC

(*
  Paxos without explicit leaders/learners.
  Messages: Prepare, Promise, Accept, Accepted, Decide.
  Quorums are strict majorities; thus any two quorums intersect.
  Liveness is set to FALSE, reflecting that termination is not guaranteed
  in an asynchronous model with failures (FLP).
*)

CONSTANTS
  Proposers,    \* set of proposers
  Acceptors,    \* set of acceptors
  Ballots,      \* totally ordered ballot numbers; assumed subset of Nat
  Values,       \* set of all possible values
  Proposed,     \* subset of Values that may be legitimately proposed
  None          \* distinguished value not in Values

(*
  Basic structural assumptions.
*)
ASSUME
  /\ Proposers # {}
  /\ Acceptors # {}
  /\ Values # {}
  /\ Proposed \subseteq Values
  /\ Proposed # {}
  /\ None \notin Values
  /\ Ballots \subseteq Nat
  /\ Ballots # {}

(*
  Syntax of messages.
*)
NoBallot == -1

MsgType == {"Prepare","Promise","Accept","Accepted","Decide"}

Agent == Proposers \cup Acceptors

Msg ==
  [ type: MsgType,
    from: Agent,
    to: Agent,
    bal: Ballots \cup {NoBallot},
    aBal: Ballots \cup {NoBallot},
    val: Values \cup {None}
  ]

(*
  Majority quorums with pairwise intersection.
*)
Majority(Q) == Q \subseteq Acceptors /\ 2 * Cardinality(Q) > Cardinality(Acceptors)

(*
  State variables.
*)
VARIABLES
  msgs,        \* set of sent messages (immutable "network log")
  aMaxSeen,    \* [a \in Acceptors -> Max ballot number seen by a]
  aAccBal,     \* [a \in Acceptors -> Highest ballot accepted by a, or NoBallot]
  aAccVal,     \* [a \in Acceptors -> Value corresponding to aAccBal, or None]
  DecideVal    \* representative decided value, or None

vars == << msgs, aMaxSeen, aAccBal, aAccVal, DecideVal >>

(*
  Derived sets over the message log.
*)
PromiseSet(p, b) ==
  { m \in msgs :
      /\ m.type = "Promise"
      /\ m.to   = p
      /\ m.bal  = b }

PromisedAcceptors(p, b) ==
  { a \in Acceptors :
      \E m \in msgs :
        /\ m.type = "Promise"
        /\ m.from = a
        /\ m.to   = p
        /\ m.bal  = b }

CandidateAcceptedBals(p, b) ==
  { m.aBal : m \in PromiseSet(p, b) /\ m.aBal # NoBallot }

MaxAcceptedBal(p, b) ==
  IF CandidateAcceptedBals(p, b) = {} THEN NoBallot ELSE Max(CandidateAcceptedBals(p, b))

CandidateValues(p, b) ==
  IF MaxAcceptedBal(p, b) = NoBallot
     THEN Proposed
     ELSE { m.val : m \in PromiseSet(p, b) /\ m.aBal = MaxAcceptedBal(p, b) }

ChosenValue(p, b) ==
  CHOOSE v \in CandidateValues(p, b) : TRUE

(*
  Initial state.
*)
Init ==
  /\ msgs = {}
  /\ aMaxSeen = [ a \in Acceptors |-> NoBallot ]
  /\ aAccBal  = [ a \in Acceptors |-> NoBallot ]
  /\ aAccVal  = [ a \in Acceptors |-> None ]
  /\ DecideVal = None

(*
  Actions (each adds an appropriate message to msgs and updates acceptor/protocol state).
*)

SendPrepare ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots:
    LET m == [ type |-> "Prepare", from |-> p, to |-> a,
               bal  |-> b, aBal |-> NoBallot, val |-> None ]
    IN /\ m \notin msgs
       /\ msgs' = msgs \cup { m }
       /\ UNCHANGED << aMaxSeen, aAccBal, aAccVal, DecideVal >>

SendPromise ==
  \E prep \in msgs:
    /\ prep.type = "Prepare"
    /\ prep.from \in Proposers
    /\ prep.to   \in Acceptors
    /\ prep.bal  \in Ballots
    /\ prep.bal > aMaxSeen[prep.to]
    /\ LET a == prep.to
           p == prep.from
           b == prep.bal
           m == [ type |-> "Promise", from |-> a, to |-> p,
                  bal  |-> b, aBal |-> aAccBal[a], val |-> aAccVal[a] ]
       IN /\ m \notin msgs
          /\ msgs' = msgs \cup { m }
          /\ aMaxSeen' = [aMaxSeen EXCEPT ![a] = b]
          /\ UNCHANGED << aAccBal, aAccVal, DecideVal >>

SendAcceptReq ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots:
    LET GoodAs == PromisedAcceptors(p, b)
    IN /\ Majority(GoodAs)
       /\ LET v == ChosenValue(p, b)
              m == [ type |-> "Accept", from |-> p, to |-> a,
                     bal  |-> b, aBal |-> NoBallot, val |-> v ]
          IN /\ m \notin msgs
             /\ msgs' = msgs \cup { m }
             /\ UNCHANGED << aMaxSeen, aAccBal, aAccVal, DecideVal >>

DoAccept ==
  \E a \in Acceptors, p \in Proposers, b \in Ballots, v \in Values:
    LET req == [ type |-> "Accept",   from |-> p, to |-> a,
                 bal  |-> b, aBal |-> NoBallot, val |-> v ]
        m   == [ type |-> "Accepted", from |-> a, to |-> p,
                 bal  |-> b, aBal |-> NoBallot, val |-> v ]
    IN /\ req \in msgs
       /\ b >= aMaxSeen[a]
       /\ m \notin msgs
       /\ msgs' = msgs \cup { m }
       /\ aMaxSeen' = [aMaxSeen EXCEPT ![a] = b]
       /\ aAccBal'  = [aAccBal  EXCEPT ![a] = b]
       /\ aAccVal'  = [aAccVal  EXCEPT ![a] = v]
       /\ UNCHANGED DecideVal

Decide ==
  \E p \in Proposers, b \in Ballots, v \in Values:
    /\ DecideVal = None
    /\ LET S == { a \in Acceptors :
                    \E m \in msgs :
                      /\ m.type = "Accepted"
                      /\ m.from = a
                      /\ m.to   = p
                      /\ m.bal  = b
                      /\ m.val  = v }
       IN /\ Majority(S)
          /\ LET dm == [ type |-> "Decide", from |-> p, to |-> p,
                         bal  |-> b, aBal |-> NoBallot, val |-> v ]
             IN /\ dm \notin msgs
                /\ msgs' = msgs \cup { dm }
                /\ DecideVal' = v
                /\ UNCHANGED << aMaxSeen, aAccBal, aAccVal >>

Next ==
  SendPrepare
  \/ SendPromise
  \/ SendAcceptReq
  \/ DoAccept
  \/ Decide

(*
  Safety invariants and temporal consistency property.
*)
TypeOK ==
  /\ msgs \subseteq Msg
  /\ aMaxSeen \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ aAccBal  \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ aAccVal  \in [Acceptors -> Values \cup {None}]
  /\ DecideVal \in Values \cup {None}

NonTriviality ==
  DecideVal \in {None} \cup Proposed

(*
  Consistency-related temporal property:
  Once a decision is made (DecideVal # None), the decided value never changes.
*)
ConsistencyTemporal ==
  [] (DecideVal # None => [DecideVal' = DecideVal]_vars)

(*
  Specification and liveness.
*)
Spec ==
  Init /\ [][Next]_vars

Liveness == FALSE

=============================================================================
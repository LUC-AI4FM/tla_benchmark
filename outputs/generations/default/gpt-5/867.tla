----------------------------- MODULE PaxosNoLeaders -----------------------------

EXTENDS Naturals, FiniteSets

(*
  Paxos consensus without explicit leaders or learners.
  Messages: Prepare, Promise, Accept, Accepted, Decide.
  State tracks all sent messages, a representative decision value (Decision),
  and per-acceptor highest seen ballot (maxSeen), highest accepted ballot (accBal),
  and corresponding accepted value (accVal).

  Quorums are strict majorities and thus pairwise intersect.
  Liveness is explicitly set to FALSE; Paxos does not guarantee termination
  under asynchronous faults (FLP).
*)

CONSTANTS
  Proposer,  \* nonempty set of proposers
  Acceptor,  \* nonempty set of acceptors
  Value,     \* nonempty set of application values
  Proposed,  \* nonempty subset of Value that may be proposed
  None       \* distinguished element not in Value, used as "no value"

ASSUME /\ Proposer # {}
       /\ Acceptor # {}
       /\ Value # {}
       /\ Proposed \subseteq Value
       /\ Proposed # {}
       /\ None \notin Value

(*
  Ballots are natural numbers.
  We use None to denote "no ballot/value recorded".
*)
Ballot      == Nat
BalOrNone   == Ballot \cup {None}
ValOrNone   == Value \cup {None}

(*
  Helpers for comparing/updating ballots when "None" is possible.
*)
GeqBal(b, x) == x = None \/ b >= x
MaxBal(x, b) == IF x = None THEN b ELSE IF b > x THEN b ELSE x

(*
  Quorums are strict majorities, which guarantees pairwise intersection.
*)
Majority(Q) == Q \subseteq Acceptor /\ 2 * Cardinality(Q) > Cardinality(Acceptor)
Quorums     == { Q \in SUBSET Acceptor : Majority(Q) }

QuorumAssumption == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME QuorumAssumption

(*
  Message schemas
*)
PrepareMsgs ==
  { [type |-> "Prepare", from |-> p, to |-> a, bal |-> b]
    : p \in Proposer, a \in Acceptor, b \in Ballot }

PromiseMsgs ==
  { [type |-> "Promise", from |-> a, to |-> p, bal |-> b, accBal |-> ab, accVal |-> av]
    : a \in Acceptor, p \in Proposer, b \in Ballot, ab \in BalOrNone, av \in ValOrNone }

AcceptMsgs ==
  { [type |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> v]
    : p \in Proposer, a \in Acceptor, b \in Ballot, v \in Value }

AcceptedMsgs ==
  { [type |-> "Accepted", from |-> a, to |-> p, bal |-> b, val |-> v]
    : a \in Acceptor, p \in Proposer, b \in Ballot, v \in Value }

DecideMsgs ==
  { [type |-> "Decide", bal |-> b, val |-> v]
    : b \in Ballot, v \in Value }

AllMsgs == PrepareMsgs \cup PromiseMsgs \cup AcceptMsgs \cup AcceptedMsgs \cup DecideMsgs

VARIABLES
  msgs,       \* set of sent messages (undelivered/observed abstractly)
  maxSeen,    \* [Acceptor -> BalOrNone], highest prepare/accept ballot seen (promised)
  accBal,     \* [Acceptor -> BalOrNone], highest accepted ballot
  accVal,     \* [Acceptor -> ValOrNone], value corresponding to accBal
  Decision    \* ValOrNone, representative learned/decided value

vars == << msgs, maxSeen, accBal, accVal, Decision >>

(*
  Type correctness
*)
TypeOK ==
  /\ msgs \subseteq AllMsgs
  /\ maxSeen \in [Acceptor -> BalOrNone]
  /\ accBal  \in [Acceptor -> BalOrNone]
  /\ accVal  \in [Acceptor -> ValOrNone]
  /\ Decision \in ValOrNone
  /\ \A a \in Acceptor : (accBal[a] = None) <=> (accVal[a] = None)

(*
  Initial state: no messages, no promises/accepts, no decision.
*)
Init ==
  /\ msgs = {}
  /\ maxSeen = [a \in Acceptor |-> None]
  /\ accBal  = [a \in Acceptor |-> None]
  /\ accVal  = [a \in Acceptor |-> None]
  /\ Decision = None

(*
  Actions
*)

SendPrepare ==
  \E p \in Proposer, a \in Acceptor, b \in Ballot :
    /\ msgs' = msgs \cup { [type |-> "Prepare", from |-> p, to |-> a, bal |-> b] }
    /\ UNCHANGED << maxSeen, accBal, accVal, Decision >>

SendPromise ==
  \E a \in Acceptor, p \in Proposer, b \in Ballot :
    /\ \E m \in msgs :
         /\ m.type = "Prepare"
         /\ m.from = p
         /\ m.to   = a
         /\ m.bal  = b
    /\ GeqBal(b, maxSeen[a])
    /\ LET newMS == [maxSeen EXCEPT ![a] = MaxBal(@[a], b)] IN
       /\ maxSeen' = newMS
       /\ msgs' = msgs \cup {
            [ type   |-> "Promise",
              from   |-> a,
              to     |-> p,
              bal    |-> b,
              accBal |-> accBal[a],
              accVal |-> accVal[a] ] }
       /\ UNCHANGED << accBal, accVal, Decision >>

SendAcceptsFromPromises ==
  \E p \in Proposer, b \in Ballot, Q \in Quorums :
    /\ \A a \in Q :
         \E pm \in msgs :
           /\ pm.type = "Promise"
           /\ pm.from = a
           /\ pm.to   = p
           /\ pm.bal  = b
    /\ LET Pms == { pm \in msgs :
                     pm.type = "Promise" /\ pm.to = p /\ pm.bal = b /\ pm.from \in Q } IN
       LET S == { pm.accBal : pm \in Pms /\ pm.accBal # None } IN
       LET chosenV ==
            IF S = {} THEN CHOOSE v \in Proposed : TRUE
            ELSE
              LET mx == Max(S)
                  Vs == { pm.accVal : pm \in Pms /\ pm.accBal = mx }
              IN CHOOSE v \in Vs : TRUE
       IN
       /\ msgs' = msgs \cup { [type |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> chosenV] : a \in Q }
       /\ UNCHANGED << maxSeen, accBal, accVal, Decision >>

RecvAcceptAndSendAccepted ==
  \E a \in Acceptor, p \in Proposer, b \in Ballot, v \in Value :
    /\ [type |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> v] \in msgs
    /\ GeqBal(b, maxSeen[a])
    /\ maxSeen' = [maxSeen EXCEPT ![a] = MaxBal(@[a], b)]
    /\ accBal'  = [accBal  EXCEPT ![a] = b]
    /\ accVal'  = [accVal  EXCEPT ![a] = v]
    /\ msgs' = msgs \cup {
         [ type |-> "Accepted", from |-> a, to |-> p, bal |-> b, val |-> v ] }
    /\ UNCHANGED Decision

SendDecide ==
  \E b \in Ballot, v \in Value, Q \in Quorums :
    /\ \A a \in Q :
         \E am \in msgs :
           /\ am.type = "Accepted"
           /\ am.from = a
           /\ am.bal  = b
           /\ am.val  = v
    /\ msgs' = msgs \cup { [type |-> "Decide", bal |-> b, val |-> v] }
    /\ UNCHANGED << maxSeen, accBal, accVal, Decision >>

LearnDecision ==
  \E S \in SUBSET DecideMsgs :
    /\ S \subseteq msgs
    /\ S # {}
    /\ Decision = None
    /\ Decision' \in { m.val : m \in S }
    /\ UNCHANGED << msgs, maxSeen, accBal, accVal >>

Next ==
  SendPrepare
  \/ SendPromise
  \/ SendAcceptsFromPromises
  \/ RecvAcceptAndSendAccepted
  \/ SendDecide
  \/ LearnDecision

Spec == Init /\ [][Next]_vars

(*
  Safety invariants
*)
OnlyProposedCanBeLearned ==
  Decision = None \/ Decision \in Proposed

DecideMsgsAgree ==
  \A m1 \in msgs :
    \A m2 \in msgs :
      (m1.type = "Decide" /\ m2.type = "Decide") => m1.val = m2.val

Inv == TypeOK /\ OnlyProposedCanBeLearned /\ DecideMsgsAgree

(*
  Consistency-related temporal property over the Decision variable:
  Once Decision is set to a value, it never changes (stability).
*)
DecConsistency == [](Decision = None \/ Decision' = Decision)

(*
  Liveness explicitly disabled: Paxos does not guarantee termination in
  asynchronous systems with faults (FLP).
*)
Liveness == FALSE

=============================================================================
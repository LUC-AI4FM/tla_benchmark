----------------------------- MODULE PaxosClassic -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  REPLICAS, \* exactly four processes
  BALLOTS,  \* a set of natural-number ballots including 0
  VALUES,   \* application values
  NoValue   \* distinguished value not in VALUES

ASSUME
  /\ REPLICAS # {} /\ Cardinality(REPLICAS) = 4
  /\ BALLOTS \subseteq Nat /\ 0 \in BALLOTS
  /\ NoValue \notin VALUES

(***************************************************************************)
(* Basic definitions                                                       *)
(***************************************************************************)

MSGTYPE == {"1a", "1b", "2a", "2b"}

Message ==
  [ type   : MSGTYPE,
    from   : REPLICAS,
    to     : REPLICAS,
    ballot : BALLOTS,
    vbal   : BALLOTS,               \* previously accepted ballot (0 if none)
    value  : VALUES \cup {NoValue}  \* carried value (NoValue if none)
  ]

Quorums == { Q \in SUBSET REPLICAS : Cardinality(Q) = 3 }

\* Max of a non-empty finite subset of Nat
MaxIn(S) == CHOOSE x \in S : \A y \in S : y <= x

MaxVBal(QMsgs) ==
  MaxIn({ m.vbal : m \in QMsgs })

ForcedValue(QMsgs) ==
  IF \E m \in QMsgs : m.vbal > 0 THEN
    CHOOSE v \in VALUES :
      \E m \in QMsgs : m.vbal = MaxVBal(QMsgs) /\ v = m.value
  ELSE
    CHOOSE v \in VALUES : TRUE

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  messages,    \* set of messages in the system
  maxBallot,   \* [REPLICAS -> BALLOTS], highest seen (promised) ballot
  maxVBallot,  \* [REPLICAS -> BALLOTS], highest ballot at which a value was accepted
  maxValue,    \* [REPLICAS -> (VALUES \cup {NoValue})], value accepted at maxVBallot
  decision     \* single learned decision value (NoValue if none)

vars == << messages, maxBallot, maxVBallot, maxValue, decision >>

TypeOK ==
  /\ messages \subseteq Message
  /\ maxBallot \in [REPLICAS -> BALLOTS]
  /\ maxVBallot \in [REPLICAS -> BALLOTS]
  /\ maxValue \in [REPLICAS -> (VALUES \cup {NoValue})]
  /\ decision \in (VALUES \cup {NoValue})

Proposed ==
  { m.value : m \in messages /\ m.type = "2a" /\ m.value \in VALUES }

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ messages = {}
  /\ maxBallot = [a \in REPLICAS |-> 0]
  /\ maxVBallot = [a \in REPLICAS |-> 0]
  /\ maxValue = [a \in REPLICAS |-> NoValue]
  /\ decision = NoValue
  /\ TypeOK

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

PaxosPrepare ==
  \E p \in REPLICAS, b \in (BALLOTS \ {0}) :
    LET out == { [ type   |-> "1a",
                   from   |-> p,
                   to     |-> a,
                   ballot |-> b,
                   vbal   |-> 0,
                   value  |-> NoValue ] : a \in REPLICAS }
    IN
      /\ messages' = messages \cup out
      /\ UNCHANGED << maxBallot, maxVBallot, maxValue, decision >>

PaxosPromise ==
  \E a \in REPLICAS, m \in messages :
    /\ m.type = "1a"
    /\ m.to = a
    /\ m.ballot > maxBallot[a]
    /\ LET b == m.ballot
           p == m.from
           out == { [ type   |-> "1b",
                      from   |-> a,
                      to     |-> p,
                      ballot |-> b,
                      vbal   |-> maxVBallot[a],
                      value  |-> maxValue[a] ] }
       IN
         /\ messages' = messages \cup out
         /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
         /\ UNCHANGED << maxVBallot, maxValue, decision >>

PaxosAccept ==
  \E p \in REPLICAS, b \in (BALLOTS \ {0}), Q \in Quorums :
    /\ \A a \in Q :
         \E m \in messages :
           m.type = "1b" /\ m.to = p /\ m.ballot = b /\ m.from = a
    /\ LET QMsgs == { m \in messages :
                        m.type = "1b" /\ m.to = p /\ m.ballot = b /\ m.from \in Q }
           v == ForcedValue(QMsgs)
           out == { [ type   |-> "2a",
                      from   |-> p,
                      to     |-> a,
                      ballot |-> b,
                      vbal   |-> 0,
                      value  |-> v ] : a \in REPLICAS }
       IN
         /\ messages' = messages \cup out
         /\ UNCHANGED << maxBallot, maxVBallot, maxValue, decision >>

PaxosAccepted ==
  \E a \in REPLICAS, m \in messages :
    /\ m.type = "2a"
    /\ m.to = a
    /\ m.ballot >= maxBallot[a]
    /\ LET b == m.ballot
           v == m.value
           out == { [ type   |-> "2b",
                      from   |-> a,
                      to     |-> r,
                      ballot |-> b,
                      vbal   |-> b,
                      value  |-> v ] : r \in REPLICAS }
       IN
         /\ messages' = messages \cup out
         /\ maxBallot' = [maxBallot EXCEPT ![a] = b]
         /\ maxVBallot' = [maxVBallot EXCEPT ![a] = b]
         /\ maxValue' = [maxValue EXCEPT ![a] = v]
         /\ UNCHANGED decision

PaxosDecide ==
  /\ decision = NoValue
  /\ \E Q \in Quorums, b \in (BALLOTS \ {0}), v \in VALUES :
       \A a \in Q :
         \E m \in messages :
           m.type = "2b" /\ m.from = a /\ m.ballot = b /\ m.value = v
  /\ decision' = v
  /\ UNCHANGED << messages, maxBallot, maxVBallot, maxValue >>

Next ==
  PaxosPrepare \/ PaxosPromise \/ PaxosAccept \/ PaxosAccepted \/ PaxosDecide

Spec ==
  Init /\ [][Next]_vars /\ SF_vars(PaxosDecide)

(***************************************************************************)
(* Safety and liveness properties                                          *)
(***************************************************************************)

PaxosNontriviality ==
  decision = NoValue \/ decision \in Proposed

PaxosConsistency ==
  [] (decision = NoValue \/ decision' = decision)

Liveness ==
  FALSE

=============================================================================
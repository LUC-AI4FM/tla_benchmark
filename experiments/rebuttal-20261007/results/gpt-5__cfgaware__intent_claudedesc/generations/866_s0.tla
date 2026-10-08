--------------------------- MODULE FastPaxos ---------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Acceptors,        \* set of acceptor replicas
  Coordinator,      \* distinguished coordinator (not used operationally in this abstraction)
  Values,           \* set of client values
  FastQuorums,      \* set of fast quorums (subsets of Acceptors)
  ClassicQuorums,   \* set of classic quorums (subsets of Acceptors)
  Bot               \* distinguished "no value" marker, not in Values

(*
  Quorum and typing assumptions reflecting the request:
  - Fast quorums are subsets of Acceptors
  - Any two fast quorums intersect
  - Fast quorums contain at least three-quarters of Acceptors
  - Any classic quorum intersects with any fast quorum (and thus with any two)
  - Basic finiteness/typing assumptions
*)
ASSUME
  /\ Coordinator \notin Acceptors
  /\ Finite(Acceptors) /\ Cardinality(Acceptors) >= 1
  /\ Finite(Values) /\ Values # {}
  /\ Bot \notin Values
  /\ FastQuorums \subseteq SUBSET Acceptors /\ FastQuorums # {}
  /\ ClassicQuorums \subseteq SUBSET Acceptors /\ ClassicQuorums # {}
  /\ \A F1 \in FastQuorums: \A F2 \in FastQuorums: (F1 \cap F2) # {}
  /\ \A F \in FastQuorums:
        4 * Cardinality(F) >= 3 * Cardinality(Acceptors)
  /\ \A C \in ClassicQuorums:
        \A F \in FastQuorums: (C \cap F) # {}

(***************************************************************************)
(* State Variables                                                         *)
(***************************************************************************)

VARIABLES
  fastRoundActive,   \* BOOLEAN: whether the fast round is currently enabled
  fastVotes,         \* [Acceptors -> (Values \cup {Bot})]: votes cast in the fast round
  classicActive,     \* BOOLEAN: whether a classic round is active
  classicValue,      \* (Values \cup {Bot}): value selected by coordinator for classic round
  classicVotes,      \* [Acceptors -> (Values \cup {Bot})]: votes in the classic round
  decided            \* (Values \cup {Bot}): decided value if any

vars == << fastRoundActive, fastVotes, classicActive, classicValue, classicVotes, decided >>

(***************************************************************************)
(* Derived sets and predicates                                             *)
(***************************************************************************)

ProposedInFast ==
  { v \in Values : \E a \in Acceptors: fastVotes[a] = v }

HasFastUnanimity(v) ==
  \E F \in FastQuorums: \A a \in F: fastVotes[a] = v

FastDecidable ==
  \E v \in Values: HasFastUnanimity(v)

Collision ==
  \E a \in Acceptors:
    \E b \in Acceptors:
      /\ fastVotes[a] \in Values
      /\ fastVotes[b] \in Values
      /\ fastVotes[a] # fastVotes[b]

MajorityWithinSomeFast(v) ==
  \E F \in FastQuorums:
    2 * Cardinality({ a \in F: fastVotes[a] = v }) > Cardinality(F)

ClassicDecidable ==
  /\ classicActive
  /\ classicValue \in Values
  /\ \E C \in ClassicQuorums: \A a \in C: classicVotes[a] = classicValue

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ fastRoundActive = FALSE
  /\ fastVotes \in [Acceptors -> (Values \cup {Bot})]
  /\ \A a \in Acceptors: fastVotes[a] = Bot
  /\ classicActive = FALSE
  /\ classicValue = Bot
  /\ classicVotes \in [Acceptors -> (Values \cup {Bot})]
  /\ \A a \in Acceptors: classicVotes[a] = Bot
  /\ decided = Bot

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

StartFast ==
  /\ ~fastRoundActive
  /\ ~classicActive
  /\ decided = Bot
  /\ fastRoundActive' = TRUE
  /\ UNCHANGED << fastVotes, classicActive, classicValue, classicVotes, decided >>

FastVote(a, v) ==
  /\ fastRoundActive
  /\ decided = Bot
  /\ a \in Acceptors
  /\ v \in Values
  /\ fastVotes[a] = Bot
  /\ fastVotes' = [fastVotes EXCEPT ![a] = v]
  /\ UNCHANGED << fastRoundActive, classicActive, classicValue, classicVotes, decided >>

FastDecision ==
  /\ decided = Bot
  /\ \E v \in Values: HasFastUnanimity(v)
  /\ LET v0 == CHOOSE v \in Values: HasFastUnanimity(v)
     IN decided' = v0
  /\ UNCHANGED << fastRoundActive, fastVotes, classicActive, classicValue, classicVotes >>

StartClassic ==
  /\ ~classicActive
  /\ decided = Bot
  /\ Collision
  /\ ~FastDecidable
  /\ LET forcedVals ==
        { v \in Values : MajorityWithinSomeFast(v) }
     IN /\ IF forcedVals # {}
           THEN classicValue' \in forcedVals
           ELSE classicValue' \in ProposedInFast
  /\ classicActive' = TRUE
  /\ fastRoundActive' = FALSE
  /\ UNCHANGED << fastVotes, classicVotes, decided >>

ClassicVote(a) ==
  /\ classicActive
  /\ decided = Bot
  /\ a \in Acceptors
  /\ classicValue \in Values
  /\ classicVotes[a] = Bot
  /\ classicVotes' = [classicVotes EXCEPT ![a] = classicValue]
  /\ UNCHANGED << fastRoundActive, fastVotes, classicActive, classicValue, decided >>

ClassicDecision ==
  /\ decided = Bot
  /\ ClassicDecidable
  /\ decided' = classicValue
  /\ UNCHANGED << fastRoundActive, fastVotes, classicActive, classicValue, classicVotes >>

Next ==
  \/ StartFast
  \/ \E a \in Acceptors: \E v \in Values: FastVote(a, v)
  \/ FastDecision
  \/ StartClassic
  \/ \E a \in Acceptors: ClassicVote(a)
  \/ ClassicDecision

(***************************************************************************)
(* Required operators for model checking                                   *)
(***************************************************************************)

FastSpec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(FastDecision)
  /\ WF_vars(ClassicDecision)

FastTypeOK ==
  /\ fastRoundActive \in BOOLEAN
  /\ fastVotes \in [Acceptors -> (Values \cup {Bot})]
  /\ classicActive \in BOOLEAN
  /\ classicValue \in (Values \cup {Bot})
  /\ classicVotes \in [Acceptors -> (Values \cup {Bot})]
  /\ decided \in (Values \cup {Bot})

FastNontriviality ==
  (decided \in Values) => (decided \in ProposedInFast)

PaxosConsistency ==
  \A v1 \in Values: \A v2 \in Values:
    /\ (HasFastUnanimity(v1) \/ (\E C \in ClassicQuorums: \A a \in C: classicVotes[a] = v1))
    /\ (HasFastUnanimity(v2) \/ (\E C \in ClassicQuorums: \A a \in C: classicVotes[a] = v2))
    => v1 = v2

=============================================================================
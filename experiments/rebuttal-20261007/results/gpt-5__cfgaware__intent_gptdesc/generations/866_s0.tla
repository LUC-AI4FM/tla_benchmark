----------------------------- MODULE FastPaxos -----------------------------
EXTENDS Naturals, FiniteSets

(*
  Abstract Fast Paxos for one consensus instance.
  Roles: proposers, acceptors, and an abstract coordinator (used only for classic rounds).
  Two round types:
    - Fast round: proposers broadcast values; acceptors may accept any proposed value.
      A decision occurs when a fast quorum of acceptors report the same value.
    - Classic round: coordinator resolves collisions from a preceding fast round.
      If some value appears in a strict majority of a chosen fast quorum's responses,
      the coordinator must choose that value; otherwise it may choose any proposed value.
  Safety:
    - Agreement (PaxosConsistency)
    - Nontriviality (FastNontriviality)
    - Valid conflict-resolution rule is enforced by construction (ChooseClassicCandidate).
  Liveness: asynchronous message delivery; weak fairness on decision steps.
*)

CONSTANTS
  Proposers,           \* set of proposers
  Acceptors,           \* set of acceptors (replicas)
  Coordinators,        \* set of potential coordinators (role is abstract; not explicitly modeled as a variable)
  Values,              \* set of application values
  FastQuorums,         \* a set of fast quorums, each a nonempty subset of Acceptors
  ClassicQuorums       \* a set of classic (majority) quorums, each a nonempty subset of Acceptors

(*
  Quorum structure assumptions (constants discipline).
  - Acceptors are finite.
  - Classic quorums are strict majorities and intersect pairwise.
  - Fast quorums are nonempty, intersect pairwise, and intersect every classic quorum.
*)
QuorumAx ==
  /\ IsFinite(Acceptors)
  /\ FastQuorums \subseteq SUBSET Acceptors
  /\ ClassicQuorums \subseteq SUBSET Acceptors
  /\ \A F \in FastQuorums: F # {}
  /\ \A C \in ClassicQuorums: C # {}
  /\ \A C \in ClassicQuorums: Cardinality(C) > Cardinality(Acceptors) / 2
  /\ \A C1, C2 \in ClassicQuorums: C1 \cap C2 # {}
  /\ \A F1, F2 \in FastQuorums: F1 \cap F2 # {}
  /\ \A F \in FastQuorums: \A C \in ClassicQuorums: F \cap C # {}

ASSUME QuorumAx

(*
  Using Maybe-Values as subsets of Values of size at most 1.
  {} denotes "no value", {v} denotes "the value v".
*)
IsMaybe(M) == M \in SUBSET Values /\ Cardinality(M) <= 1

(*
  State variables
*)
VARIABLES
  Proposed,           \* set of values proposed by proposers
  fastActive,         \* is a fast round active?
  classicActive,      \* is a classic round active?
  fastAccepted,       \* [a \in Acceptors |-> {} or {v}] last value accepted by a in the fast round
  reports,            \* [a \in Acceptors |-> {} or {v}] coordinator's received report from a (if delivered)
  ReportsDelivered,   \* subset of Acceptors that have delivered their report to the coordinator (for current classic round)
  chosenFQ,           \* the fast quorum chosen by the coordinator for collision resolution in current classic round
  classicCandidate,   \* {} or {v}; coordinator's chosen value for classic round
  classicVotes,       \* [a \in Acceptors |-> {} or {v}] classic accept votes
  Decided             \* {} or {v}; the decided value (once nonempty, never changes)

vars ==
  << Proposed, fastActive, classicActive, fastAccepted, reports, ReportsDelivered,
     chosenFQ, classicCandidate, classicVotes, Decided >>

(*
  Typing invariant
*)
FastTypeOK ==
  /\ Proposed \subseteq Values
  /\ fastActive \in BOOLEAN
  /\ classicActive \in BOOLEAN
  /\ fastAccepted \in [Acceptors -> SUBSET Values]
  /\ \A a \in Acceptors: Cardinality(fastAccepted[a]) <= 1
  /\ reports \in [Acceptors -> SUBSET Values]
  /\ \A a \in Acceptors: Cardinality(reports[a]) <= 1
  /\ ReportsDelivered \subseteq Acceptors
  /\ chosenFQ \subseteq Acceptors
  /\ classicActive => chosenFQ \in FastQuorums
  /\ IsMaybe(classicCandidate)
  /\ classicVotes \in [Acceptors -> SUBSET Values]
  /\ \A a \in Acceptors: Cardinality(classicVotes[a]) <= 1
  /\ IsMaybe(Decided)
  /\ QuorumAx

(*
  Consensus goal: at most one value v \in Values is ever decided for this instance.
  Safety properties below formalize agreement and nontriviality.
*)

(*
  Helper predicates for decisions
*)
FastDecided(v) ==
  \E F \in FastQuorums:
    \A a \in F: fastAccepted[a] = {v}

ClassicDecided(v) ==
  \E C \in ClassicQuorums:
    \A a \in C: classicVotes[a] = {v}

(*
  Agreement: no two different values can both become decided (by any mix of fast/classic).
*)
PaxosConsistency ==
  \A v1, v2 \in Values:
    v1 # v2 =>
      ~(
        (FastDecided(v1) /\ FastDecided(v2))
        \/
        (FastDecided(v1) /\ ClassicDecided(v2))
        \/
        (ClassicDecided(v1) /\ ClassicDecided(v2))
      )

(*
  Nontriviality: only values ever proposed may be decided.
  Since Decided is {} or {v}, this asserts any decided v is in Proposed.
*)
FastNontriviality ==
  Decided \subseteq Proposed

(*
  Initial state
*)
Init ==
  /\ Proposed = {}
  /\ fastActive = FALSE
  /\ classicActive = FALSE
  /\ fastAccepted = [a \in Acceptors |-> {}]
  /\ reports = [a \in Acceptors |-> {}]
  /\ ReportsDelivered = {}
  /\ chosenFQ = {}
  /\ classicCandidate = {}
  /\ classicVotes = [a \in Acceptors |-> {}]
  /\ Decided = {}

(*
  Actions
*)

StartFast ==
  /\ ~fastActive
  /\ ~classicActive
  /\ Decided = {}
  /\ fastActive' = TRUE
  /\ UNCHANGED << Proposed, classicActive, fastAccepted, reports, ReportsDelivered,
                  chosenFQ, classicCandidate, classicVotes, Decided >>

Propose ==
  \E p \in Proposers, v \in Values:
    /\ fastActive
    /\ Proposed' = Proposed \cup {v}
    /\ UNCHANGED << fastActive, classicActive, fastAccepted, reports, ReportsDelivered,
                    chosenFQ, classicCandidate, classicVotes, Decided >>

AcceptFast ==
  \E a \in Acceptors, v \in Proposed:
    /\ fastActive
    /\ ~classicActive
    /\ fastAccepted' = [fastAccepted EXCEPT ![a] = {v}]
    /\ UNCHANGED << Proposed, fastActive, classicActive, reports, ReportsDelivered,
                    chosenFQ, classicCandidate, classicVotes, Decided >>

DecideFast ==
  \E v \in Values, F \in FastQuorums:
    /\ Decided = {}
    /\ \A a \in F: fastAccepted[a] = {v}
    /\ Decided' = {v}
    /\ UNCHANGED << Proposed, fastActive, classicActive, fastAccepted, reports, ReportsDelivered,
                    chosenFQ, classicCandidate, classicVotes >>

StartClassic ==
  /\ ~classicActive
  /\ Decided = {}
  /\ classicActive' = TRUE
  /\ chosenFQ' \in FastQuorums
  /\ reports' = [a \in Acceptors |-> {}]
  /\ ReportsDelivered' = {}
  /\ classicVotes' = [a \in Acceptors |-> {}]
  /\ classicCandidate' = {}
  /\ UNCHANGED << Proposed, fastActive, fastAccepted, Decided >>

DeliverReport ==
  \E a \in Acceptors:
    /\ classicActive
    /\ a \in chosenFQ
    /\ ~(a \in ReportsDelivered)
    /\ reports' = [reports EXCEPT ![a] = fastAccepted[a]]
    /\ ReportsDelivered' = ReportsDelivered \cup {a}
    /\ UNCHANGED << Proposed, fastActive, classicActive, fastAccepted, chosenFQ,
                    classicCandidate, classicVotes, Decided >>

ChooseClassicCandidate ==
  /\ classicActive
  /\ classicCandidate = {}
  /\ LET MajVals ==
        { v \in Values :
            Cardinality({ a \in chosenFQ :
                            a \in ReportsDelivered /\ reports[a] = {v} })
            > Cardinality(chosenFQ) / 2
        }
     IN IF MajVals # {}
        THEN \E v \in MajVals: classicCandidate' = {v}
        ELSE \E v \in Proposed: classicCandidate' = {v}
  /\ UNCHANGED << Proposed, fastActive, classicActive, fastAccepted, reports,
                  ReportsDelivered, chosenFQ, classicVotes, Decided >>

AcceptClassic ==
  \E a \in Acceptors, v \in Values:
    /\ classicActive
    /\ classicCandidate = {v}
    /\ classicVotes' = [classicVotes EXCEPT ![a] = {v}]
    /\ UNCHANGED << Proposed, fastActive, classicActive, fastAccepted, reports,
                    ReportsDelivered, chosenFQ, classicCandidate, Decided >>

DecideClassic ==
  \E v \in Values, C \in ClassicQuorums:
    /\ Decided = {}
    /\ classicActive
    /\ classicCandidate = {v}
    /\ \A a \in C: classicVotes[a] = {v}
    /\ Decided' = {v}
    /\ UNCHANGED << Proposed, fastActive, classicActive, fastAccepted, reports,
                    ReportsDelivered, chosenFQ, classicCandidate, classicVotes >>

(*
  Validity of conflict resolution (expressed as a derived invariant):
  If a strict majority for some value is already evident among delivered reports
  of the chosen fast quorum, then the classic candidate (if chosen) must be that value.
*)
ValidConflictResolution ==
  ~(classicActive /\ classicCandidate # {})
  \/
  LET MajVals ==
        { v \in Values :
            Cardinality({ a \in chosenFQ :
                            a \in ReportsDelivered /\ reports[a] = {v} })
            > Cardinality(chosenFQ) / 2
        }
  IN (MajVals = {}) \/ (classicCandidate \subseteq MajVals)

Next ==
    StartFast
  \/ Propose
  \/ AcceptFast
  \/ DecideFast
  \/ StartClassic
  \/ DeliverReport
  \/ ChooseClassicCandidate
  \/ AcceptClassic
  \/ DecideClassic

FastSpec ==
  Init /\ [][Next]_vars
    /\ WF_vars(DecideFast)
    /\ WF_vars(DecideClassic)

=============================================================================
----------------------------- MODULE FastPaxos -----------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  A,                 \* Set of acceptors (replicas)
  COORD,             \* Unique designated coordinator
  VALUES,            \* Nonempty set of values
  FastBallots,       \* Disjoint set of fast ballots
  ClassicBallots,    \* Disjoint set of classic ballots
  FQuorums,          \* Set of fast quorums (subsets of A)
  CQuorums,          \* Set of classic quorums (subsets of A)
  NoValue,           \* Distinguished non-value
  NoVote,            \* Distinguished non-vote mark
  NoBallot           \* Distinguished non-ballot

ASSUME
  /\ COORD \notin A
  /\ A # {}
  /\ VALUES # {}
  /\ FastBallots # {} /\ ClassicBallots # {}
  /\ FastBallots \cap ClassicBallots = {}
  /\ NoValue \notin VALUES
  /\ NoVote \notin VALUES
  /\ NoBallot \notin (FastBallots \cup ClassicBallots)
  /\ FQuorums \subseteq SUBSET A /\ FQuorums # {}
  /\ CQuorums \subseteq SUBSET A /\ CQuorums # {}
  /\ \A Q1 \in FQuorums: \A Q2 \in FQuorums: Q1 \cap Q2 # {}
  /\ \A Qc \in CQuorums: \A Qf \in FQuorums: Qc \cap Qf # {}
  /\ \A Q \in FQuorums:
        Cardinality(Q) >= ((3 * Cardinality(A)) + 3) \div 4

Ballots == FastBallots \cup ClassicBallots

MinFastSize == ((3 * Cardinality(A)) + 3) \div 4

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  mode,               \* "idle", "fast", "classic", "decided"
  cur,                \* current active ballot or NoBallot
  votes,              \* [Ballots -> [A -> (VALUES \cup {NoVote})]]
  proposedInFast,     \* [FastBallots -> SUBSET VALUES]
  startedFast,        \* SUBSET FastBallots
  startedClassic,     \* SUBSET ClassicBallots
  resolveOf,          \* [ClassicBallots -> (FastBallots \cup {NoBallot})]
  selectedForClassic, \* [ClassicBallots -> (VALUES \cup {NoValue})]
  decidedValue        \* VALUES \cup {NoValue}

vars == << mode, cur, votes, proposedInFast, startedFast, startedClassic, resolveOf, selectedForClassic, decidedValue >>

(***************************************************************************)
(* Helper predicates and operators                                         *)
(***************************************************************************)

TypeOK ==
  /\ mode \in {"idle","fast","classic","decided"}
  /\ cur \in (Ballots \cup {NoBallot})
  /\ votes \in [Ballots -> [A -> (VALUES \cup {NoVote})]]
  /\ proposedInFast \in [FastBallots -> SUBSET VALUES]
  /\ startedFast \subseteq FastBallots
  /\ startedClassic \subseteq ClassicBallots
  /\ resolveOf \in [ClassicBallots -> (FastBallots \cup {NoBallot})]
  /\ selectedForClassic \in [ClassicBallots -> (VALUES \cup {NoValue})]
  /\ decidedValue \in (VALUES \cup {NoValue})

VotedSet(f) == { votes[f][a] : a \in A /\ votes[f][a] \in VALUES }

AllSameOn(f, Q, v) ==
  v \in VALUES /\ \A a \in Q: votes[f][a] = v

DecidableFast(f) ==
  \E v \in VALUES: \E Q \in FQuorums: AllSameOn(f, Q, v)

FastDecisionValue(f) ==
  CHOOSE v \in VALUES: \E Q \in FQuorums: AllSameOn(f, Q, v)

Collision(f) ==
  \E a \in A: \E b \in A:
    /\ votes[f][a] \in VALUES
    /\ votes[f][b] \in VALUES
    /\ votes[f][a] # votes[f][b]

NoFastDecisionPossible(f) == ~ DecidableFast(f)

MajorityIn(Q, f, v) ==
  /\ Q \in FQuorums
  /\ v \in VALUES
  /\ Cardinality({ a \in Q: votes[f][a] = v }) > (Cardinality(Q) \div 2)

AnyFastQuorum == CHOOSE Q \in FQuorums: TRUE

PickValueForClassic(f) ==
  LET Q == AnyFastQuorum IN
    IF \E v \in VALUES: MajorityIn(Q, f, v)
    THEN CHOOSE v \in VALUES: MajorityIn(Q, f, v)
    ELSE CHOOSE v \in proposedInFast[f]: TRUE

ClassicDecidable(c) ==
  /\ c \in ClassicBallots
  /\ selectedForClassic[c] \in VALUES
  /\ \E Qc \in CQuorums: \A a \in Qc: votes[c][a] = selectedForClassic[c]

ProposedAll == UNION { proposedInFast[f] : f \in FastBallots }

DecidedFast(v) ==
  \E f \in startedFast:
    \E Q \in FQuorums: AllSameOn(f, Q, v)

DecidedClassic(v) ==
  \E c \in startedClassic:
    /\ selectedForClassic[c] = v
    /\ \E Qc \in CQuorums: \A a \in Qc: votes[c][a] = v

Decided(v) == DecidedFast(v) \/ DecidedClassic(v)

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
  /\ mode = "idle"
  /\ cur = NoBallot
  /\ votes \in [Ballots -> [A -> (VALUES \cup {NoVote})]]
  /\ \A b \in Ballots: \A a \in A: votes[b][a] = NoVote
  /\ proposedInFast \in [FastBallots -> SUBSET VALUES]
  /\ \A f \in FastBallots: proposedInFast[f] = {}
  /\ startedFast = {}
  /\ startedClassic = {}
  /\ resolveOf \in [ClassicBallots -> (FastBallots \cup {NoBallot})]
  /\ \A c \in ClassicBallots: resolveOf[c] = NoBallot
  /\ selectedForClassic \in [ClassicBallots -> (VALUES \cup {NoValue})]
  /\ \A c \in ClassicBallots: selectedForClassic[c] = NoValue
  /\ decidedValue = NoValue
  /\ TypeOK

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

StartFastRound(f) ==
  /\ mode = "idle"
  /\ f \in FastBallots \ startedFast
  /\ mode' = "fast"
  /\ cur' = f
  /\ startedFast' = startedFast \cup { f }
  /\ UNCHANGED << votes, proposedInFast, startedClassic, resolveOf, selectedForClassic, decidedValue >>

VoteFast(a) ==
  /\ mode = "fast"
  /\ a \in A
  /\ cur \in FastBallots
  /\ votes[cur][a] = NoVote
  /\ \E v \in VALUES:
       /\ votes' = [votes EXCEPT ![cur][a] = v]
       /\ proposedInFast' = [proposedInFast EXCEPT ![cur] = @ \cup { v }]
  /\ UNCHANGED << mode, cur, startedFast, startedClassic, resolveOf, selectedForClassic, decidedValue >>

DecideFast ==
  /\ mode = "fast"
  /\ cur \in FastBallots
  /\ DecidableFast(cur)
  /\ decidedValue' = FastDecisionValue(cur)
  /\ mode' = "decided"
  /\ UNCHANGED << cur, votes, proposedInFast, startedFast, startedClassic, resolveOf, selectedForClassic >>

StartClassicRound(c) ==
  /\ mode = "fast"
  /\ cur \in FastBallots
  /\ c \in ClassicBallots \ startedClassic
  /\ NoFastDecisionPossible(cur)
  /\ Collision(cur)
  /\ mode' = "classic"
  /\ cur' = c
  /\ startedClassic' = startedClassic \cup { c }
  /\ resolveOf' = [resolveOf EXCEPT ![c] = cur]
  /\ selectedForClassic' = [selectedForClassic EXCEPT ![c] = PickValueForClassic(cur)]
  /\ UNCHANGED << votes, proposedInFast, startedFast, decidedValue >>

VoteClassic(a) ==
  /\ mode = "classic"
  /\ a \in A
  /\ cur \in ClassicBallots
  /\ selectedForClassic[cur] \in VALUES
  /\ votes[cur][a] = NoVote
  /\ votes' = [votes EXCEPT ![cur][a] = selectedForClassic[cur]]
  /\ UNCHANGED << mode, cur, proposedInFast, startedFast, startedClassic, resolveOf, selectedForClassic, decidedValue >>

DecideClassic ==
  /\ mode = "classic"
  /\ cur \in ClassicBallots
  /\ ClassicDecidable(cur)
  /\ decidedValue' = selectedForClassic[cur]
  /\ mode' = "decided"
  /\ UNCHANGED << cur, votes, proposedInFast, startedFast, startedClassic, resolveOf, selectedForClassic >>

Next ==
  \/ \E f \in FastBallots: StartFastRound(f)
  \/ \E a \in A: VoteFast(a)
  \/ DecideFast
  \/ \E c \in ClassicBallots: StartClassicRound(c)
  \/ \E a \in A: VoteClassic(a)
  \/ DecideClassic

(***************************************************************************)
(* Safety properties (invariants)                                          *)
(***************************************************************************)

AgreementInv ==
  \A v \in VALUES: \A w \in VALUES: (Decided(v) /\ Decided(w)) => v = w

DecisionVarSound ==
  decidedValue = NoValue \/ Decided(decidedValue)

ValidityInv ==
  decidedValue = NoValue \/ decidedValue \in ProposedAll

Safety == AgreementInv /\ DecisionVarSound /\ ValidityInv

(***************************************************************************)
(* Liveness and Fairness                                                   *)
(***************************************************************************)

Liveness ==
  /\ \A a \in A: WF_vars(VoteFast(a))
  /\ \A a \in A: WF_vars(VoteClassic(a))
  /\ \A f \in FastBallots: WF_vars(StartFastRound(f))
  /\ \A c \in ClassicBallots: WF_vars(StartClassicRound(c))
  /\ WF_vars(DecideFast)
  /\ WF_vars(DecideClassic)

Spec ==
  Init /\ [][Next]_vars /\ Liveness

=============================================================================
------------------------------ MODULE FastPaxosSimplified ------------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  VALUES, PROPOSERS, ACCEPTORS, LEARNERS,
  Coordinator,        \* unique coordinator
  RoundNums,          \* totally ordered round identifiers
  FastRounds,         \* subset of rounds that are "fast"
  ClassicRounds,      \* subset of rounds that are "classic"
  QC,                 \* family of classic quorums (set of nonempty subsets of ACCEPTORS)
  QF,                 \* family of fast quorums (set of nonempty subsets of ACCEPTORS)
  DefaultVal,         \* an arbitrary default value in VALUES, used to initialize reportV
  Null                \* a distinguished value not in VALUES

(*
  Assumptions about constants and quorum intersection properties
*)
ASSUME
  /\ Coordinator \in PROPOSERS
  /\ Null \notin VALUES
  /\ DefaultVal \in VALUES
  /\ FastRounds \subseteq RoundNums
  /\ ClassicRounds \subseteq RoundNums
  /\ FastRounds \cap ClassicRounds = {}
  /\ FastRounds \cup ClassicRounds = RoundNums
  /\ QC \subseteq SUBSET(ACCEPTORS)
  /\ QF \subseteq SUBSET(ACCEPTORS)
  /\ QC # {} /\ QF # {}
  /\ \A Q \in QC: Q # {}
  /\ \A F \in QF: F # {}
  /\ \A Q1 \in QC, Q2 \in QC: Q1 \cap Q2 # {}      \* classic quorums intersect
  /\ \A F \in QF, Q \in QC: F \cap Q # {}          \* every fast quorum intersects every classic quorum

(*
  State variables
*)
VARIABLES
  proposed,     \* set of proposed values
  promised,     \* [ACCEPTORS -> RoundNums \cup {-1}], highest round promised by each acceptor
  votes,        \* set of vote records [a: ACCEPTORS, r: RoundNums, v: VALUES]
  currRound,    \* current classic round the coordinator is working on (or -1 if none)
  prepQ,        \* [ClassicRounds -> SUBSET(ACCEPTORS)], chosen classic prepare quorum for each classic round ({} if none)
  reportR,      \* [ClassicRounds -> [ACCEPTORS -> (RoundNums \cup {-1})]], reported highest round<r per acceptor at prepare
  reportV,      \* [ClassicRounds -> [ACCEPTORS -> VALUES]], value associated with reportR (meaningful only if reportR>=0)
  classicProp   \* [ClassicRounds -> (VALUES \cup {Null})], coordinator's chosen value for each classic round, or Null if none

vars == << proposed, promised, votes, currRound, prepQ, reportR, reportV, classicProp >>

(*
  Helper definitions
*)
RoundsBot == RoundNums \cup {-1}

Max(S) == CHOOSE m \in S: \A n \in S: n <= m

HasVote(a, r) == \E v \in VALUES: [a |-> a, r |-> r, v |-> v] \in votes

VoteVal(a, r) ==
  IF HasVote(a, r)
  THEN CHOOSE v \in VALUES: [a |-> a, r |-> r, v |-> v] \in votes
  ELSE Null

MaxRoundBelow(a, c) ==
  Max(({ r \in RoundNums: r < c /\ HasVote(a, r) } \cup {-1}))

Decided(r, v) ==
  IF r \in ClassicRounds
  THEN \E C \in QC: \A a \in C: VoteVal(a, r) = v
  ELSE IF r \in FastRounds
  THEN \E F \in QF: \A a \in F: VoteVal(a, r) = v
  ELSE FALSE

Chosen(v) == \E r \in RoundNums: Decided(r, v)

SafeVals(r) ==
  LET C == prepQ[r] IN
  IF C = {}
  THEN {}                                      \* not prepared yet
  ELSE
    LET RMax == Max({ reportR[r][a] : a \in C } \cup {-1}) IN
    IF RMax = -1
    THEN proposed
    ELSE IF RMax \in ClassicRounds
         THEN { reportV[r][a] : a \in C /\ reportR[r][a] = RMax }
         ELSE
           LET Smax == { reportV[r][a] : a \in C /\ reportR[r][a] = RMax } IN
           IF Cardinality(Smax) = 1
           THEN Smax
           ELSE { v \in proposed :
                    \E F \in QF:
                      \A a \in (F \cap C):
                        (reportR[r][a] # RMax) \/ (reportV[r][a] = v)
                }

(*
  Initialization
*)
Init ==
  /\ proposed = {}
  /\ promised \in [ACCEPTORS -> {-1}]
  /\ votes = {}
  /\ currRound = -1
  /\ prepQ = [r \in ClassicRounds |-> {}]
  /\ reportR = [r \in ClassicRounds |-> [a \in ACCEPTORS |-> -1]]
  /\ reportV = [r \in ClassicRounds |-> [a \in ACCEPTORS |-> DefaultVal]]
  /\ classicProp = [r \in ClassicRounds |-> Null]

(*
  Protocol actions
*)

\* Any proposer may submit a value to be considered
Submit(p, v) ==
  /\ p \in PROPOSERS
  /\ v \in VALUES
  /\ v \notin proposed
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED << promised, votes, currRound, prepQ, reportR, reportV, classicProp >>

\* Fast path: any proposer sends v for a fast round r; acceptors vote directly
FastAccept(a, r, v) ==
  /\ a \in ACCEPTORS
  /\ r \in FastRounds
  /\ v \in proposed
  /\ promised[a] <= r
  /\ ~HasVote(a, r)
  /\ votes' = votes \cup { [a |-> a, r |-> r, v |-> v] }
  /\ promised' = [promised EXCEPT ![a] = r]
  /\ UNCHANGED << proposed, currRound, prepQ, reportR, reportV, classicProp >>

\* Coordinator starts a classic round r: choose a classic quorum, collect highest prior votes
StartClassic(r) ==
  /\ r \in ClassicRounds
  /\ r > currRound
  /\ \E C \in QC:
       LET newRRow == [aa \in ACCEPTORS |-> IF aa \in C THEN MaxRoundBelow(aa, r) ELSE reportR[r][aa]] IN
       LET newVRow == [aa \in ACCEPTORS |-> IF aa \in C /\ newRRow[aa] # -1 THEN VoteVal(aa, newRRow[aa]) ELSE reportV[r][aa]] IN
       /\ prepQ' = [prepQ EXCEPT ![r] = C]
       /\ reportR' = [reportR EXCEPT ![r] = newRRow]
       /\ reportV' = [reportV EXCEPT ![r] = newVRow]
       /\ currRound' = r
       /\ UNCHANGED << proposed, promised, votes, classicProp >>

\* Coordinator chooses a safe value for the current classic round, handling fast-round collisions safely
ChooseClassic ==
  /\ currRound \in ClassicRounds
  /\ prepQ[currRound] \in QC
  /\ classicProp[currRound] = Null
  /\ SafeVals(currRound) # {}
  /\ classicProp' = [classicProp EXCEPT ![currRound] = CHOOSE v \in SafeVals(currRound): TRUE]
  /\ UNCHANGED << proposed, promised, votes, currRound, prepQ, reportR, reportV >>

\* Acceptors accept the coordinator's classic proposal for the current round
ClassicAccept(a) ==
  /\ a \in ACCEPTORS
  /\ currRound \in ClassicRounds
  /\ classicProp[currRound] \in VALUES
  /\ promised[a] <= currRound
  /\ IF HasVote(a, currRound)
     THEN /\ votes' = votes
          /\ promised' = [promised EXCEPT ![a] = currRound]
     ELSE /\ votes' = votes \cup { [a |-> a, r |-> currRound, v |-> classicProp[currRound]] }
          /\ promised' = [promised EXCEPT ![a] = currRound]
  /\ UNCHANGED << proposed, currRound, prepQ, reportR, reportV, classicProp >>

(*
  Next-state relation
*)
Next ==
  \/ \E p \in PROPOSERS, v \in VALUES: Submit(p, v)
  \/ \E a \in ACCEPTORS, r \in FastRounds, v \in proposed: FastAccept(a, r, v)
  \/ \E r \in ClassicRounds: StartClassic(r)
  \/ ChooseClassic
  \/ \E a \in ACCEPTORS: ClassicAccept(a)

(*
  Fairness (progress) conditions
*)
CoordinatorStep == (\E r \in ClassicRounds: StartClassic(r)) \/ ChooseClassic
AcceptorStep(a) == ClassicAccept(a) \/ (\E r \in FastRounds, v \in proposed: FastAccept(a, r, v))

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(CoordinatorStep)
  /\ \A a \in ACCEPTORS: WF_vars(AcceptorStep(a))

(*
  Type and safety invariants
*)
TypeInv ==
  /\ proposed \subseteq VALUES
  /\ promised \in [ACCEPTORS -> (RoundNums \cup {-1})]
  /\ votes \subseteq [a: ACCEPTORS, r: RoundNums, v: VALUES]
  /\ currRound \in (RoundNums \cup {-1})
  /\ prepQ \in [ClassicRounds -> SUBSET(ACCEPTORS)]
  /\ \A r \in ClassicRounds: (prepQ[r] = {}) \/ (prepQ[r] \in QC)
  /\ reportR \in [ClassicRounds -> [ACCEPTORS -> (RoundNums \cup {-1})]]
  /\ reportV \in [ClassicRounds -> [ACCEPTORS -> VALUES]]
  /\ classicProp \in [ClassicRounds -> (VALUES \cup {Null})]

OneVotePerRound ==
  \A a \in ACCEPTORS: \A r \in RoundNums:
    \A v1 \in VALUES: \A v2 \in VALUES:
      (([a |-> a, r |-> r, v |-> v1] \in votes) /\ ([a |-> a, r |-> r, v |-> v2] \in votes))
        => v1 = v2

PromiseCoversVotes ==
  \A a \in ACCEPTORS: \A r \in RoundNums: \A v \in VALUES:
    ([a |-> a, r |-> r, v |-> v] \in votes) => promised[a] >= r

\* Non-triviality: only proposed values can be decided
NonTriviality == \A v \in VALUES: Chosen(v) => v \in proposed

\* Agreement: at most one value can be decided
Agreement == \A v1 \in VALUES: \A v2 \in VALUES: (Chosen(v1) /\ Chosen(v2)) => v1 = v2

Safety == TypeInv /\ OneVotePerRound /\ PromiseCoversVotes /\ NonTriviality /\ Agreement

(*
  Liveness: eventually, some value is decided (under the given fairness conditions)
*)
Termination == <> (\E v \in VALUES: Chosen(v))

=============================================================================
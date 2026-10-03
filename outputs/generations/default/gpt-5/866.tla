--------------------------- MODULE FastPaxosSimplified ---------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  Acceptors,        \* Nonempty finite set of acceptors
  Proposers,        \* Nonempty set of proposers
  Values,           \* Nonempty set of values
  Coordinator,      \* Unique coordinator, an element of Proposers
  FastQuorums,      \* Set of fast quorums: subsets of Acceptors
  ClassicQuorums,   \* Set of classic quorums: subsets of Acceptors
  K,                \* Lower bound on |F ∩ C| for F∈FastQuorums, C∈ClassicQuorums
  None              \* Distinguished value not in Values

\* Basic structural assumptions about the system and quorum families
ASSUME
  /\ Coordinator \in Proposers
  /\ None \notin Values
  /\ FastQuorums \subseteq SUBSET Acceptors
  /\ ClassicQuorums \subseteq SUBSET Acceptors
  /\ \A C \in ClassicQuorums : C /= {}
  /\ \A F \in FastQuorums   : F /= {}
  \* Classic quorums pairwise intersect
  /\ \A C1 \in ClassicQuorums : \A C2 \in ClassicQuorums : C1 \cap C2 /= {}
  \* Fast quorums pairwise intersect (prevents two distinct fast decisions)
  /\ \A F1 \in FastQuorums : \A F2 \in FastQuorums : F1 \cap F2 /= {}
  \* Fast-classic intersection lower bound
  /\ K \in Nat /\ K > 0
  /\ \A F \in FastQuorums : \A C \in ClassicQuorums : Cardinality(F \cap C) >= K

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  proposed,     \* Set of values that have been proposed
  promised,     \* [Acceptors -> Int], highest round promised by each acceptor
  acceptedRnd,  \* [Acceptors -> Int], last round in which each acceptor accepted
  acceptedVal,  \* [Acceptors -> (Values \cup {None})], corresponding accepted value
  coordR,       \* Coordinator's current classic round number (>0 for classic rounds)
  chosenV,      \* Value chosen by coordinator for the current classic round (or None)
  decided       \* Decided value (or None if not yet decided)

NoRound == -1
FastRound == 0

vars == << proposed, promised, acceptedRnd, acceptedVal, coordR, chosenV, decided >>

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)

MaxSet(S) == CHOOSE m \in S : \A x \in S : x <= m

MaxPromised() == MaxSet({ promised[a] : a \in Acceptors })

Votes(C, v) == Cardinality({ a \in C : acceptedRnd[a] = FastRound /\ acceptedVal[a] = v })

\* Safe value selection in a classic round from a classic quorum C,
\* honoring both prior classic-round accepts and fast-round collisions.
ChooseSafe(C) ==
  LET S == { acceptedRnd[a] : a \in C } IN
  LET M == MaxSet(S) IN
    IF M > 0 THEN
      \* If any accept in the highest classic round M was observed, choose its value
      CHOOSE v \in { acceptedVal[a] : a \in C /\ acceptedRnd[a] = M /\ acceptedVal[a] \in Values } : TRUE
    ELSE
      IF \E v \in Values : Votes(C, v) >= K THEN
        \* Some value might have been fast-decided; choose one with at least K votes in C
        CHOOSE v \in { w \in Values : Votes(C, w) >= K } : TRUE
      ELSE
        \* Nothing constrains safety; any proposed value is safe (or None if none proposed yet)
        IF proposed /= {} THEN CHOOSE v \in proposed : TRUE ELSE None

\* Predicates describing that a value has a deciding quorum of accepts in the current state
FastDecided(v) ==
  \E F \in FastQuorums : \A a \in F : acceptedRnd[a] = FastRound /\ acceptedVal[a] = v

ClassicDecided(v) ==
  \E r \in Nat : r > 0 /\ \E C \in ClassicQuorums :
    \A a \in C : acceptedRnd[a] = r /\ acceptedVal[a] = v

Decidable(v) == FastDecided(v) \/ ClassicDecided(v)

(***************************************************************************)
(* Initial condition                                                       *)
(***************************************************************************)

Init ==
  /\ proposed = {}
  /\ promised = [a \in Acceptors |-> NoRound]
  /\ acceptedRnd = [a \in Acceptors |-> NoRound]
  /\ acceptedVal = [a \in Acceptors |-> None]
  /\ coordR = 0
  /\ chosenV = None
  /\ decided = None

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Propose(p, v) ==
  /\ p \in Proposers
  /\ v \in Values
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED << promised, acceptedRnd, acceptedVal, coordR, chosenV, decided >>

FastAccept(a, v) ==
  /\ a \in Acceptors
  /\ v \in proposed
  /\ promised[a] <= FastRound
  /\ acceptedRnd' = [acceptedRnd EXCEPT ![a] = FastRound]
  /\ acceptedVal' = [acceptedVal EXCEPT ![a] = v]
  /\ promised'   = [b \in Acceptors |-> IF b = a /\ promised[b] < FastRound THEN FastRound ELSE promised[b]]
  /\ UNCHANGED << proposed, coordR, chosenV, decided >>

StartClassic(C) ==
  /\ C \in ClassicQuorums
  /\ LET r == MaxPromised() + 1 IN
       /\ coordR' = r
       /\ chosenV' = ChooseSafe(C)
       /\ promised' = [a \in Acceptors |-> IF a \in C /\ promised[a] < r THEN r ELSE promised[a]]
       /\ UNCHANGED << proposed, acceptedRnd, acceptedVal, decided >>

ClassicAccept(a) ==
  /\ a \in Acceptors
  /\ chosenV # None
  /\ promised[a] <= coordR
  /\ acceptedRnd' = [acceptedRnd EXCEPT ![a] = coordR]
  /\ acceptedVal' = [acceptedVal EXCEPT ![a] = chosenV]
  /\ promised'   = [b \in Acceptors |-> IF b = a /\ promised[b] < coordR THEN coordR ELSE promised[b]]
  /\ UNCHANGED << proposed, coordR, chosenV, decided >>

DecideFast ==
  /\ decided = None
  /\ \E v \in Values : \E F \in FastQuorums :
        \A a \in F : acceptedRnd[a] = FastRound /\ acceptedVal[a] = v
  /\ decided' = CHOOSE v \in Values :
        \E F \in FastQuorums : \A a \in F : acceptedRnd[a] = FastRound /\ acceptedVal[a] = v
  /\ UNCHANGED << proposed, promised, acceptedRnd, acceptedVal, coordR, chosenV >>

DecideClassic ==
  /\ decided = None
  /\ \E r \in Nat : r > 0 /\ \E v \in Values : \E C \in ClassicQuorums :
        \A a \in C : acceptedRnd[a] = r /\ acceptedVal[a] = v
  /\ decided' = CHOOSE v \in Values :
        \E r \in Nat : r > 0 /\ \E C \in ClassicQuorums :
           \A a \in C : acceptedRnd[a] = r /\ acceptedVal[a] = v
  /\ UNCHANGED << proposed, promised, acceptedRnd, acceptedVal, coordR, chosenV >>

Next ==
  \E p \in Proposers : \E v \in Values : Propose(p, v)
  \/ \E a \in Acceptors : \E v \in proposed : FastAccept(a, v)
  \/ \E C \in ClassicQuorums : StartClassic(C)
  \/ \E a \in Acceptors : ClassicAccept(a)
  \/ DecideFast
  \/ DecideClassic

StartClassicAny == \E C \in ClassicQuorums : StartClassic(C)
ClassicAcceptAny == \E a \in Acceptors : ClassicAccept(a)
DecideAny == DecideFast \/ DecideClassic

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(StartClassicAny)
  /\ WF_vars(ClassicAcceptAny)
  /\ WF_vars(DecideAny)

(***************************************************************************)
(* Invariants (safety)                                                     *)
(***************************************************************************)

TypeOK ==
  /\ proposed \subseteq Values
  /\ promised \in [Acceptors -> Int]
  /\ \A a \in Acceptors : promised[a] = NoRound \/ promised[a] \in Nat
  /\ acceptedRnd \in [Acceptors -> Int]
  /\ \A a \in Acceptors : acceptedRnd[a] = NoRound \/ acceptedRnd[a] \in Nat
  /\ acceptedVal \in [Acceptors -> (Values \cup {None})]
  /\ \A a \in Acceptors : (acceptedRnd[a] = NoRound) => (acceptedVal[a] = None)
  /\ \A a \in Acceptors : (acceptedRnd[a] \in Nat) => (acceptedVal[a] \in Values)
  /\ coordR \in Nat
  /\ chosenV \in (Values \cup {None})
  /\ decided \in (Values \cup {None})

AcceptedOnlyProposed ==
  \A a \in Acceptors : acceptedVal[a] = None \/ acceptedVal[a] \in proposed

ChosenOnlyProposed ==
  chosenV = None \/ chosenV \in proposed

NonTriviality ==
  decided = None \/ decided \in proposed

\* Agreement: at most one value is (fast- or classic-)decidable in any state
Agreement ==
  \A v1 \in Values : \A v2 \in Values :
    (Decidable(v1) /\ Decidable(v2)) => v1 = v2

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

DecisionMade == decided # None

\* Non-blocking liveness: once some value has been proposed, eventually a value is decided.
Termination == (proposed # {}) ~> DecisionMade

=============================================================================
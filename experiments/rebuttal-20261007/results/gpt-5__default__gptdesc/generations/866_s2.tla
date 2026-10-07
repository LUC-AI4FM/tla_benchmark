----------------------------- MODULE FastPaxosSimplified -----------------------------

EXTENDS Naturals, Integers

CONSTANTS
  Acceptors,          \* Non-empty set of acceptors
  Proposers,          \* Non-empty set of proposers
  Coordinator,        \* Unique coordinator (an element of Proposers)
  Values,             \* Non-empty set of values
  None,               \* A distinguished value not in Values, used to denote "no vote"
  QF,                 \* Set of fast quorums, i.e., a set of non-empty subsets of Acceptors
  QC,                 \* Set of classic quorums, i.e., a set of non-empty subsets of Acceptors
  FRound,             \* A designated fast round (a natural number)
  CRound              \* A designated classic round (a natural number, greater than FRound)

ASSUME
  /\ Coordinator \in Proposers
  /\ None \notin Values
  /\ FRound \in Nat /\ CRound \in Nat /\ FRound < CRound /\ FRound # CRound
  /\ QF \subseteq SUBSET Acceptors /\ QC \subseteq SUBSET Acceptors
  /\ \A f \in QF: f # {} /\ \A c \in QC: c # {}
  /\ \A c1 \in QC: \A c2 \in QC: (c1 \cap c2) # {}
  /\ \A f1 \in QF: \A f2 \in QF: (f1 \cap f2) # {}
  /\ \A f \in QF: \A c \in QC: (f \cap c) # {}

Rounds == {FRound, CRound}
IsFast(r) == r = FRound
IsClassic(r) == r = CRound

(*
 Helper: maximum of a non-empty set of integers.
*)
Max(S) == CHOOSE m \in S: \A n \in S: m >= n

VARIABLES
  Proposed,    \* Subset of Values that have been proposed
  Vote,        \* [a \in Acceptors -> [r \in Rounds -> Values \cup {None}]]
  Promised     \* [a \in Acceptors -> {-1} \cup Rounds], max round "promised"/seen

vars == << Proposed, Vote, Promised >>

Init ==
  /\ Proposed = {}
  /\ Vote = [a \in Acceptors |-> [r \in Rounds |-> None]]
  /\ Promised = [a \in Acceptors |-> -1]

(*
 A proposer introduces a value into the system. Only proposed values may be voted on.
*)
Propose ==
  \E p \in Proposers, v \in Values:
    /\ v \notin Proposed
    /\ Proposed' = Proposed \cup {v}
    /\ Vote' = Vote
    /\ Promised' = Promised

(*
 Fast round vote: any proposer can send directly; an acceptor votes if it has not
 already voted in FRound and has not promised a higher round.
*)
FastVote ==
  \E a \in Acceptors, v \in Proposed:
    /\ Promised[a] <= FRound
    /\ Vote[a][FRound] = None
    /\ Vote' = [Vote EXCEPT ![a][FRound] = v]
    /\ Promised' = [Promised EXCEPT ![a] = FRound]
    /\ Proposed' = Proposed

(*
 Safe value selection for the classic round, incorporating collision handling:
 - If no prior votes exist in rounds < CRound, any proposed value is safe.
 - Otherwise, let k be the greatest prior round with any vote. Since we model only
   one fast round FRound (< CRound), k is FRound if any fast votes exist.
   * If some value satisfies the Fast Paxos "wins" condition (it is consistent with
     every fast quorum: in each fast quorum at least one member voted for it or did not vote),
     the coordinator must choose such a value.
   * Otherwise, any proposed value is safe.
*)
SafeClassic(v) ==
  /\ v \in Proposed
  /\ LET KSet == { k \in Rounds : k < CRound /\ \E a \in Acceptors: Vote[a][k] # None } IN
     IF KSet = {} THEN TRUE
     ELSE
       LET k == Max(KSet) IN
         IF k = FRound THEN
           LET Wins(w) == \A f \in QF: \E a \in f: Vote[a][FRound] = w \/ Vote[a][FRound] = None IN
             IF \E w \in Values: Wins(w)
               THEN Wins(v)
               ELSE TRUE
         ELSE
           FALSE  \* No other prior rounds are modeled

(*
 Classic round accept: the coordinator selects a classic quorum C and a value v that
 satisfies SafeClassic, and has all acceptors in C vote for v in CRound (assuming no
 higher promise and no prior vote at CRound).
*)
ClassicAccept ==
  \E C \in QC, v \in Proposed:
    /\ \A a \in C: Promised[a] <= CRound /\ Vote[a][CRound] = None
    /\ SafeClassic(v)
    /\ Vote' =
         [ a \in Acceptors |->
             [ r \in Rounds |->
                 IF r = CRound /\ a \in C THEN v ELSE Vote[a][r] ] ]
    /\ Promised' =
         [ a \in Acceptors |->
             IF a \in C THEN CRound ELSE Promised[a] ]
    /\ Proposed' = Proposed

Next == Propose \/ FastVote \/ ClassicAccept

Spec == Init /\ [][Next]_vars

(*
 Derived predicates for chosen values.
 A value is chosen in the fast round if some fast quorum voted for it in FRound.
 A value is chosen in the classic round if some classic quorum voted for it in CRound.
*)
ChosenFast(v) == \E f \in QF: \A a \in f: Vote[a][FRound] = v
ChosenClassic(v) == \E c \in QC: \A a \in c: Vote[a][CRound] = v
Chosen(v) == ChosenFast(v) \/ ChosenClassic(v)

(*
 Type invariants and safety properties.
*)
TypeOK ==
  /\ Proposed \subseteq Values
  /\ Vote \in [Acceptors -> [Rounds -> Values \cup {None}]]
  /\ Promised \in [Acceptors -> Int]
  /\ \A a \in Acceptors: Promised[a] \in {-1} \cup Rounds
  /\ \A a \in Acceptors: \A r \in Rounds: Vote[a][r] # None => Promised[a] >= r

NonTriviality ==
  \A v \in Values: Chosen(v) => v \in Proposed

Agreement ==
  \A v1 \in Values: \A v2 \in Values:
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

=====================================================================================
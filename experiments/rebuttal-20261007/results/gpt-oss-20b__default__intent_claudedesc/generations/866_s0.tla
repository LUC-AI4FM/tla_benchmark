MODULE FastPaxos
EXTENDS Naturals

CONSTANTS Acceptors, Values, FastQuorums, ClassicQuorums

ASSUME
  /\ Acceptors ≠ {}
  /\ Values ≠ {}
  /\ FastQuorums ⊆ SUBSET[Acceptors]
  /\ ClassicQuorums ⊆ SUBSET[Acceptors]

VARIABLES accVote, decVal, round

(* Type invariant *)
TypeInvariant ==
  /\ accVote ∈ [Acceptors → Values ∪ {⊥}]
  /\ decVal ∈ Values ∪ {⊥}
  /\ round ∈ [type: {"fast","classic"}, num: Nat]

Init ==
  TypeInvariant
  /\ accVote = [a ∈ Acceptors |-> ⊥]
  /\ decVal = ⊥
  /\ round = [type |-> "fast", num |-> 0]

(* Helper predicates *)
FastQuorum(q) == q ∈ FastQuorums
ClassicQuorum(q) == q ∈ ClassicQuorums

StartFastRound ==
  /\ round.type' = "fast"
  /\ round.num' = round.num + 1
  /\ accVote' = [a ∈ Acceptors |-> ⊥]
  /\ UNCHANGED <<decVal>>

StartClassicRound ==
  /\ round.type = "fast"
  /\ decVal = ⊥
  /\ ¬∃ q ∈ FastQuorums : ∃ v ∈ Values : (∀ a ∈ q : accVote[a] = v)
  /\ round.type' = "classic"
  /\ round.num' = round.num + 1
  /\ accVote' = [a ∈ Acceptors |-> ⊥]
  /\ UNCHANGED <<decVal>>

VoteFast(acc, v) ==
  /\ round.type = "fast"
  /\ decVal = ⊥
  /\ acc ∈ Acceptors
  /\ v ∈ Values
  /\ accVote[acc] = ⊥ \/ accVote[acc] = v
  /\ accVote' = [accVote EXCEPT ![acc] = v]
  /\ UNCHANGED <<decVal, round>>

VoteClassic(acc, v) ==
  /\ round.type = "classic"
  /\ decVal = ⊥
  /\ acc ∈ Acceptors
  /\ v ∈ Values
  /\ accVote' = [accVote EXCEPT ![acc] = v]
  /\ UNCHANGED <<decVal, round>>

DecideFast ==
  /\ round.type = "fast"
  /\ decVal = ⊥
  /\ ∃ q ∈ FastQuorums : ∃ v ∈ Values : (∀ a ∈ q : accVote[a] = v)
  /\ LET chosen == CHOOSE v ∈ Values :
        (∃ q ∈ FastQuorums : ∀ a ∈ q : accVote[a] = v) IN
       decVal' = chosen
  /\ UNCHANGED <<accVote, round>>

DecideClassic ==
  /\ round.type = "classic"
  /\ decVal = ⊥
  /\ ∃ q ∈ ClassicQuorums : ∃ v ∈ Values : (∀ a ∈ q : accVote[a] = v)
  /\ LET chosen == CHOOSE v ∈ Values :
        (∃ q ∈ ClassicQuorums : ∀ a ∈ q : accVote[a] = v) IN
       decVal' = chosen
  /\ UNCHANGED <<accVote, round>>

Next ==
  \/ StartFastRound
  \/ StartClassicRound
  \/ ∃ acc ∈ Acceptors, v ∈ Values : VoteFast(acc,v)
  \/ ∃ acc ∈ Acceptors, v ∈ Values : VoteClassic(acc,v)
  \/ DecideFast
  \/ DecideClassic

vars == <<accVote, decVal, round>>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next) /\ NonTriviality

NonTriviality ==
  decVal ≠ ⊥ ⇒ ∃ acc ∈ Acceptors : accVote[acc] = decVal
===============================================================================
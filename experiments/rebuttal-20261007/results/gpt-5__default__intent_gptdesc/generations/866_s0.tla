------------------------------ MODULE FastPaxos ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    Proposers,        \* Set of proposers (abstract role)
    Acceptors,        \* Set of acceptors (replicas)
    Coord,            \* Set of coordinators (abstract role)
    Val,              \* Set of possible values for the single instance
    FastQuorums,      \* Set of fast quorum sets (each a subset of Acceptors)
    ClassicQuorums,   \* Set of classic quorum sets (each a subset of Acceptors)
    Null              \* Distinguished null marker, not in Val

ASSUME
    /\ FastQuorums \subseteq SUBSET Acceptors
    /\ ClassicQuorums \subseteq SUBSET Acceptors
    /\ \A F \in FastQuorums : F # {}
    /\ \A C \in ClassicQuorums : C # {}
    /\ \A F1 \in FastQuorums : \A F2 \in FastQuorums : F1 \cap F2 # {}
    /\ \A C1 \in ClassicQuorums : \A C2 \in ClassicQuorums : C1 \cap C2 # {}
    /\ \A F \in FastQuorums : \A C \in ClassicQuorums : F \cap C # {}
    /\ Null \notin Val

VARIABLES
    proposedValue,     \* [a \in Acceptors -> Val \cup {Null}]: acceptor's current proposed value
    ProposedVals,      \* Subset of Val proposed by some acceptor
    fastRoundOpen,     \* BOOLEAN: a fast round is currently open (acceptors may respond)
    fastVote,          \* [a \in Acceptors -> Val \cup {Null}]: acceptor's fast-round response
    classicRoundOpen,  \* BOOLEAN: a classic round is currently open
    coordObsF,         \* The fast quorum set observed by the coordinator when starting classic round
    chosenClassicVal,  \* Val \cup {Null}: coordinator's chosen value (per conflict-resolution rule)
    classicVote,       \* [a \in Acceptors -> Val \cup {Null}]: acceptor's classic-round acceptance
    decision           \* Val \cup {Null}: decided value for this instance (single value if decided)

vars == << proposedValue, ProposedVals, fastRoundOpen, fastVote,
           classicRoundOpen, coordObsF, chosenClassicVal, classicVote,
           decision >>

Init ==
    /\ proposedValue    = [a \in Acceptors |-> Null]
    /\ ProposedVals     = {}
    /\ fastRoundOpen    = FALSE
    /\ fastVote         = [a \in Acceptors |-> Null]
    /\ classicRoundOpen = FALSE
    /\ coordObsF        = {}
    /\ chosenClassicVal = Null
    /\ classicVote      = [a \in Acceptors |-> Null]
    /\ decision         = Null

(*
  Helper operators for fast-round majority reasoning.
*)
CountIn(F, v) == Cardinality({ a \in F : fastVote[a] = v })
StrictMajIn(F, v) == 2 * CountIn(F, v) > Cardinality(F)

(*
  Abstract proposer-to-acceptor suggestion: proposers may suggest any value
  to any acceptor, which the acceptor adopts as its current proposed value.
*)
ProposerSuggest(p, a, v) ==
    /\ p \in Proposers
    /\ a \in Acceptors
    /\ v \in Val
    /\ proposedValue' = [proposedValue EXCEPT ![a] = v]
    /\ ProposedVals'  = ProposedVals \cup {v}
    /\ UNCHANGED << fastRoundOpen, fastVote, classicRoundOpen, coordObsF,
                   chosenClassicVal, classicVote, decision >>

(*
  Fast rounds:
  - Any proposer may open a fast round (signaling "any" value may be accepted).
  - Any acceptor may respond with its current proposed value.
  - A value is decided in a fast round when some fast quorum reports the same value.
*)
StartFastRound(p) ==
    /\ p \in Proposers
    /\ fastRoundOpen' = TRUE
    /\ fastVote'      = [a \in Acceptors |-> Null]
    /\ UNCHANGED << proposedValue, ProposedVals, classicRoundOpen, coordObsF,
                   chosenClassicVal, classicVote, decision >>

FastRespond(a) ==
    /\ a \in Acceptors
    /\ fastRoundOpen
    /\ proposedValue[a] \in Val
    /\ fastVote' = [fastVote EXCEPT ![a] = proposedValue[a]]
    /\ UNCHANGED << proposedValue, ProposedVals, fastRoundOpen, classicRoundOpen,
                   coordObsF, chosenClassicVal, classicVote, decision >>

FastDecide ==
    /\ decision = Null
    /\ fastRoundOpen
    /\ \E F \in FastQuorums :
          \E v \in Val : \A a \in F : fastVote[a] = v
    /\ LET vDec == CHOOSE v \in Val :
                        \E F \in FastQuorums : \A a \in F : fastVote[a] = v
       IN decision' = vDec
    /\ fastRoundOpen' = FALSE
    /\ UNCHANGED << proposedValue, ProposedVals, fastVote, classicRoundOpen,
                   coordObsF, chosenClassicVal, classicVote >>

(*
  Classic rounds:
  - A coordinator may start a classic round after (possible) conflicts in the preceding fast round,
    selecting one fast quorum F whose responses it observes.
  - The coordinator must choose a value as follows:
      * If some value has a strict majority within F, it must choose that value.
      * Otherwise, it may choose any value among those proposed within F (i.e., values in the responses).
  - Acceptors accept the coordinator's chosen value.
  - Decision occurs when a classic quorum accepts the same value.
*)
StartClassicRound(c, F) ==
    /\ c \in Coord
    /\ F \in FastQuorums
    /\ fastRoundOpen
    /\ coordObsF'        = F
    /\ classicRoundOpen' = TRUE
    /\ fastRoundOpen'    = FALSE
    /\ chosenClassicVal' = Null
    /\ UNCHANGED << proposedValue, ProposedVals, fastVote, classicVote, decision >>

ClassicChoose ==
    /\ classicRoundOpen
    /\ coordObsF \in FastQuorums
    /\ chosenClassicVal = Null
    /\ LET F == coordObsF IN
       IF \E v \in Val : StrictMajIn(F, v)
       THEN
         /\ \E v \in Val : StrictMajIn(F, v) /\ chosenClassicVal' = v
       ELSE
         /\ \E v \in { fastVote[a] : a \in F /\ fastVote[a] \in Val } :
                chosenClassicVal' = v
    /\ UNCHANGED << proposedValue, ProposedVals, fastRoundOpen, fastVote,
                   classicRoundOpen, coordObsF, classicVote, decision >>

ClassicAccept(a) ==
    /\ a \in Acceptors
    /\ classicRoundOpen
    /\ chosenClassicVal \in Val
    /\ classicVote' = [classicVote EXCEPT ![a] = chosenClassicVal]
    /\ UNCHANGED << proposedValue, ProposedVals, fastRoundOpen, fastVote,
                   classicRoundOpen, coordObsF, chosenClassicVal, decision >>

ClassicDecide ==
    /\ decision = Null
    /\ \E C \in ClassicQuorums :
          \E v \in Val : \A a \in C : classicVote[a] = v
    /\ LET vDec == CHOOSE v \in Val :
                        \E C \in ClassicQuorums : \A a \in C : classicVote[a] = v
       IN decision' = vDec
    /\ classicRoundOpen' = FALSE
    /\ UNCHANGED << proposedValue, ProposedVals, fastRoundOpen, fastVote,
                   coordObsF, chosenClassicVal, classicVote >>

Next ==
    \/ \E p \in Proposers, a \in Acceptors, v \in Val : ProposerSuggest(p, a, v)
    \/ \E p \in Proposers : StartFastRound(p)
    \/ \E a \in Acceptors : FastRespond(a)
    \/ FastDecide
    \/ \E c \in Coord, F \in FastQuorums : StartClassicRound(c, F)
    \/ ClassicChoose
    \/ \E a \in Acceptors : ClassicAccept(a)
    \/ ClassicDecide

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(FastDecide)
    /\ WF_vars(ClassicChoose)
    /\ (\A a \in Acceptors : WF_vars(ClassicAccept(a)))
    /\ WF_vars(ClassicDecide)

(*
  Safety invariants:

  - TypeInv: basic typing of state variables.
  - FastVoteConsistencyInv: acceptors only report their current proposed value in a fast round.
  - ClassicVoteConsistencyInv: acceptors only accept the coordinator's chosen value in a classic round.
  - DecisionWellFormedInv: if a value is decided, it is a single value from Val (single-instance goal).
  - NontrivialityInv: only values actually proposed by some acceptor can be decided.
  - ValidResolutionInv: coordinator's choice respects the fast-quorum majority rule or picks among proposed-in-F values.
*)
TypeInv ==
    /\ proposedValue \in [Acceptors -> Val \cup {Null}]
    /\ ProposedVals \subseteq Val
    /\ fastRoundOpen \in BOOLEAN
    /\ fastVote \in [Acceptors -> Val \cup {Null}]
    /\ classicRoundOpen \in BOOLEAN
    /\ coordObsF \subseteq Acceptors
    /\ chosenClassicVal \in Val \cup {Null}
    /\ classicVote \in [Acceptors -> Val \cup {Null}]
    /\ decision \in Val \cup {Null}

FastVoteConsistencyInv ==
    \A a \in Acceptors :
        fastVote[a] \in Val => fastVote[a] = proposedValue[a]

ClassicVoteConsistencyInv ==
    \A a \in Acceptors :
        classicVote[a] \in Val => /\ chosenClassicVal \in Val
                                   /\ classicVote[a] = chosenClassicVal

DecisionWellFormedInv ==
    decision = Null \/ decision \in Val

NontrivialityInv ==
    decision \in Val => decision \in ProposedVals

ValidResolutionInv ==
    (chosenClassicVal = Null)
    \/ ( /\ coordObsF \in FastQuorums
         /\ ( IF (\E v \in Val : StrictMajIn(coordObsF, v))
              THEN (\E v \in Val : StrictMajIn(coordObsF, v) /\ chosenClassicVal = v)
              ELSE (chosenClassicVal \in { fastVote[a] : a \in coordObsF /\ fastVote[a] \in Val })
            )
       )

Safety ==
    TypeInv
    /\ FastVoteConsistencyInv
    /\ ClassicVoteConsistencyInv
    /\ DecisionWellFormedInv
    /\ NontrivialityInv
    /\ ValidResolutionInv

=============================================================================
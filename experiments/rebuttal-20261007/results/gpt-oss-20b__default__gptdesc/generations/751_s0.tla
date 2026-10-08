------------------------------ MODULE CigaretteSmokers ------------------------------
EXTENDS Naturals, Sequences, TLC, SetTheory

CONSTANTS INGREDIENTS, SMOKERS, MISSING, OFFERS

ASSUME
  /\ INGREDIENTS = {"tobacco", "paper", "matches"}
  /\ SMOKERS = 1..3
  /\ MISSING \in [SMOKERS -> INGREDIENTS]
  /\ OFFERS \subseteq SUBSET(INGREDIENTS)
  /\ \A o ∈ OFFERS : Cardinality(o) = 2

VARIABLES dealerOffer, smoking

MissingFromDealer(o) == FIRST(INGREDIENTS \ o)

Init ==
  /\ dealerOffer \in OFFERS
  /\ \A i ∈ SMOKERS : smoking[i] = FALSE

DealerAction ==
  \E o \in OFFERS :
    /\ ALL i ∈ SMOKERS : NOT smoking[i]
    /\ dealerOffer' = o
    /\ smoking' = smoking

SmokerAction ==
  \E sm ∈ SMOKERS :
    /\ MissingFromDealer(dealerOffer) = MISSING[sm]
    /\ NOT smoking[sm]
    /\ dealerOffer' = dealerOffer
    /\ smoking' = [i \in SMOKERS |-> IF i = sm THEN TRUE ELSE smoking[i]]

FinishAction ==
  \E sm ∈ SMOKERS :
    /\ smoking[sm]
    /\ dealerOffer' = dealerOffer
    /\ smoking' = [i \in SMOKERS |-> IF i = sm THEN FALSE ELSE smoking[i]]

Next == DealerAction \/ SmokerAction \/ FinishAction

vars == <<dealerOffer, smoking>>

FairSpec ==
  Init /\ [] (Next)_vars /\ WF_vars(Next)

AtMostOne ==
  Cardinality({i ∈ SMOKERS : smoking[i]}) <= 1

Spec == FairSpec /\ AtMostOne
=============================================================================
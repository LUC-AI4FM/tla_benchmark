----------------------------- MODULE CigaretteSmokers -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS ING, SMOKERS, Own

(*
  ING: a finite, nonempty set of ingredients.
  SMOKERS: a finite set of smokers.
  Own: a total function from SMOKERS to ING, assigning each smoker
       the unique ingredient they possess. We assume a bijection so
       every ingredient is owned by exactly one smoker.
*)
ASSUME
  /\ IsFiniteSet(ING)
  /\ ING # {}
  /\ IsFiniteSet(SMOKERS)
  /\ Own \in [SMOKERS -> ING]
  /\ \A s, t \in SMOKERS : s # t => Own[s] # Own[t]
  /\ { Own[s] : s \in SMOKERS } = ING

(*
  Offers are subsets of ingredients missing exactly one ingredient.
*)
Offers == { S \in SUBSET ING : Cardinality(S) = Cardinality(ING) - 1 }

(*
  NoOffer is a distinguished value not in SUBSET ING indicating
  the absence of any offer on the table.
*)
NoOffer == "NoOffer"

(*
  For smoker s, Need(s) is the set of ingredients he needs from the table.
*)
Need(s) == ING \ {Own[s]}

VARIABLES offer, smoking

vars == << offer, smoking >>

Init ==
  /\ offer = NoOffer
  /\ smoking = {}

(*
  Dealer places an offer when there is no outstanding offer
  and no one is currently smoking.
*)
DealerPlace ==
  /\ offer = NoOffer
  /\ smoking = {}
  /\ \E off \in Offers : offer' = off
  /\ UNCHANGED smoking

(*
  Smoker s starts smoking if the current offer exactly provides
  all ingredients except the one he owns; starting consumes the offer.
*)
SmokerStart(s) ==
  /\ s \in SMOKERS
  /\ smoking = {}
  /\ offer \in Offers
  /\ offer = Need(s)
  /\ smoking' = {s}
  /\ offer' = NoOffer

(*
  Smoker s finishes smoking; after finishing, the table remains with no offer.
*)
SmokerFinish(s) ==
  /\ s \in SMOKERS
  /\ smoking = {s}
  /\ smoking' = {}
  /\ UNCHANGED offer

StartSome == \E s \in SMOKERS : SmokerStart(s)
FinishSome == \E s \in SMOKERS : SmokerFinish(s)

Next ==
  \/ DealerPlace
  \/ StartSome
  \/ FinishSome

(*
  Type and domain invariants:
  - offer is either absent or a valid offer missing exactly one ingredient.
  - smoking is a subset of SMOKERS.
  - if anyone is smoking, there is no outstanding offer.
*)
TypeOK ==
  /\ (offer = NoOffer) \/ (offer \in Offers)
  /\ smoking \subseteq SMOKERS
  /\ (smoking = {} \/ offer = NoOffer)

(*
  Safety: at most one smoker may be smoking at any given time.
*)
AtMostOne == Cardinality(smoking) <= 1

(*
  Spec includes:
  - Initial condition
  - Step relation allowing stuttering
  - Fairness:
      * DealerPlace: when the system is idle (no offer, no smoking),
        the dealer eventually places an offer (progress of offers).
      * StartSome: whenever an offer enabling some smoker is present,
        eventually some smoker starts (no offer remains forever unused).
      * FinishSome: once someone is smoking, eventually some smoker finishes.
*)
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DealerPlace)
  /\ WF_vars(StartSome)
  /\ WF_vars(FinishSome)

=============================================================================
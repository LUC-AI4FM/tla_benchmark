---- MODULE CigaretteSmokers ----
EXTENDS Naturals, TLC

CONSTANTS
  INGREDIENTS, \* Finite nonempty set of ingredients
  SMOKERS,     \* Finite nonempty set of smokers
  Own,         \* A bijection from SMOKERS to INGREDIENTS (the unique ingredient each smoker has)
  NoOffer,     \* Special value not a subset of INGREDIENTS
  NoSmoker     \* Special value not in SMOKERS

ASSUME TypeConstAssumptions ==
  /\ IsFiniteSet(INGREDIENTS) /\ INGREDIENTS # {}
  /\ IsFiniteSet(SMOKERS) /\ SMOKERS # {}
  /\ Own \in [SMOKERS -> INGREDIENTS]
  /\ \A s1, s2 \in SMOKERS : s1 # s2 => Own[s1] # Own[s2]
  /\ { Own[s] : s \in SMOKERS } = INGREDIENTS
  /\ NoSmoker \notin SMOKERS
  /\ NoOffer \notin SUBSET INGREDIENTS

VARIABLES offer, smoking

vars == << offer, smoking >>

Offers == { INGREDIENTS \ {i} : i \in INGREDIENTS }

OfferPresent == offer \in Offers

EnabledFor(s, off) == off \in Offers /\ off = INGREDIENTS \ {Own[s]}

Init ==
  /\ offer = NoOffer
  /\ smoking = NoSmoker

DealerPlace(i) ==
  /\ i \in INGREDIENTS
  /\ offer = NoOffer
  /\ smoking = NoSmoker
  /\ offer' = INGREDIENTS \ {i}
  /\ smoking' = NoSmoker

SmokerStart(s) ==
  /\ s \in SMOKERS
  /\ smoking = NoSmoker
  /\ EnabledFor(s, offer)
  /\ smoking' = s
  /\ offer' = NoOffer

SmokerFinish(s) ==
  /\ s \in SMOKERS
  /\ smoking = s
  /\ smoking' = NoSmoker
  /\ UNCHANGED offer

DealerPlaceAny == \E i \in INGREDIENTS : DealerPlace(i)
StartSome      == \E s \in SMOKERS    : SmokerStart(s)
FinishSome     == \E s \in SMOKERS    : SmokerFinish(s)

Next ==
  DealerPlaceAny
  \/ StartSome
  \/ FinishSome

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(DealerPlaceAny)
  /\ WF_vars(StartSome)
  /\ WF_vars(FinishSome)

\* Safety and type/domain invariants
TypeInv ==
  /\ offer \in Offers \cup {NoOffer}
  /\ smoking \in SMOKERS \cup {NoSmoker}

OfferIsValidSubset ==
  /\ offer = NoOffer
     \/ /\ offer \subseteq INGREDIENTS
        /\ Cardinality(INGREDIENTS \ offer) = 1

ConsumptionInv ==
  /\ smoking # NoSmoker => offer = NoOffer

AtMostOneSmoking ==
  \A s1, s2 \in SMOKERS : (s1 # s2) => ~(smoking = s1 /\ smoking = s2)

OfferEnablesExactlyOneSmoker ==
  /\ offer \in Offers => \E! s \in SMOKERS : EnabledFor(s, offer)

Safety ==
  TypeInv /\ OfferIsValidSubset /\ ConsumptionInv /\ AtMostOneSmoking /\ OfferEnablesExactlyOneSmoker

\* Liveness properties
NoUnusedOffers ==
  [] (OfferPresent => <> (smoking # NoSmoker))

SmokingTerminates ==
  [] (smoking # NoSmoker => <> (smoking = NoSmoker))

OffersProgress ==
  [] <> OfferPresent

====
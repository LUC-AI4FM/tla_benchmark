---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients

ASSUME /\ IsFiniteSet(Ingredients)
       /\ Cardinality(Ingredients) = 3

NullOffer == "None"
Smokers == Ingredients
Offers == { Ingredients \ {i} : i \in Ingredients }
Missing(offer) == CHOOSE i \in Ingredients: i \notin offer

VARIABLES Smoking, Offer

vars == << Smoking, Offer >>

TypeOK ==
  /\ Smoking \in [Smokers -> BOOLEAN]
  /\ Offer = NullOffer \/ Offer \in Offers

Init ==
  /\ TypeOK
  /\ Offer = NullOffer
  /\ \A s \in Smokers: ~Smoking[s]

DealerOffer ==
  /\ Offer = NullOffer
  /\ \A s \in Smokers: ~Smoking[s]
  /\ \E o \in Offers: Offer' = o
  /\ Smoking' = Smoking

StartSmoking ==
  /\ Offer \in Offers
  /\ \A s \in Smokers: ~Smoking[s]
  /\ LET miss == Missing(Offer) IN
     Smoking' = [ t \in Smokers |-> t = miss ]
  /\ Offer' = Offer

FinishSmoking ==
  /\ Offer \in Offers
  /\ \E s \in Smokers: Smoking[s]
  /\ Smoking' = [ t \in Smokers |-> FALSE ]
  /\ Offer' = NullOffer

Next == DealerOffer \/ StartSmoking \/ FinishSmoking

AtMostOne == Cardinality({ s \in Smokers: Smoking[s] }) <= 1

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)
====
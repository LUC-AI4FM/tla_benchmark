------------------------------ MODULE CigaretteSmokers ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANT Ingredients

Smokers == Ingredients

Offers == { o \in SUBSET Ingredients : Cardinality(Ingredients \ o) = 1 }

VARIABLES smoking, offer

vars == << smoking, offer >>

TypeOK ==
  /\ smoking \in [Smokers -> BOOLEAN]
  /\ offer \in SUBSET Ingredients
  /\ (offer = {} \/ offer \in Offers)

NoSmoking == \A s \in Smokers: ~smoking[s]

AtMostOne == Cardinality({ s \in Smokers : smoking[s] }) <= 1

Init ==
  /\ TypeOK
  /\ smoking = [s \in Smokers |-> FALSE]
  /\ offer = {}

DealerOffers ==
  /\ NoSmoking
  /\ offer = {}
  /\ \E o \in Offers: offer' = o
  /\ UNCHANGED smoking

StartSmoking ==
  /\ offer \in Offers
  /\ NoSmoking
  /\ LET s == CHOOSE t \in Smokers : t \in (Ingredients \ offer)
     IN /\ smoking' = [t \in Smokers |-> t = s]
        /\ offer' = {}

StopSmoking ==
  /\ \E s \in Smokers: smoking[s]
  /\ smoking' = [t \in Smokers |-> FALSE]
  /\ offer' = {}

Next == DealerOffers \/ StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

=============================================================================
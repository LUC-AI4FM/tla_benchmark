--------------------------- MODULE CigaretteSmokers ---------------------------

EXTENDS TLC

CONSTANT Ingredients

ASSUME Cardinality(Ingredients) = 3

Smokers == Ingredients
Offers  == { o \in SUBSET Ingredients : Cardinality(o) = Cardinality(Ingredients) - 1 }
NoOffer == {}

VARIABLES smoking, offer
vars == << smoking, offer >>

TypeOK == /\ smoking \in [Smokers -> BOOLEAN]
          /\ offer \in SUBSET Ingredients

AtMostOne == Cardinality({ s \in Smokers : smoking[s] }) <= 1

AnySmoking == \E s \in Smokers : smoking[s]

Missing(o) == CHOOSE i \in Ingredients : o = Ingredients \ {i}

Init ==
  /\ TypeOK
  /\ smoking = [ s \in Smokers |-> FALSE ]
  /\ offer = NoOffer

OfferAction ==
  /\ offer = NoOffer
  /\ ~AnySmoking
  /\ \E o \in Offers:
       /\ offer' = o
       /\ UNCHANGED smoking

StartSmoke ==
  /\ offer # NoOffer
  /\ offer \in Offers
  /\ ~AnySmoking
  /\ LET i == Missing(offer)
     IN /\ smoking' = [smoking EXCEPT ![i] = TRUE]
        /\ UNCHANGED offer

FinishSmoke ==
  /\ AnySmoking
  /\ offer' = NoOffer
  /\ smoking' = [ s \in Smokers |-> FALSE ]

Next == OfferAction \/ StartSmoke \/ FinishSmoke

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

=============================================================================
------------------------------- MODULE CigaretteSmokers ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Smokers, Ingredients

VARIABLES Smoking, Offer

ASSUME Cardinality(Smokers) = 3
ASSUME Cardinality(Ingredients) = 3
ASSUME Smokers = {s1, s2, s3}
ASSUME Ingredients = {"tobacco", "paper", "matches"}
ASSUME \A s \in Smokers: Offer[s] \subseteq Ingredients /\ Cardinality(Offer[s]) = 2

Init == 
    /\ Smoking = {}
    /\ \A s \in Smokers: Offer[s] = {}

Next ==
    \/ \E s \in Smokers, i \in (Ingredients \ Offer[s]): 
        Smoking' = {s}
        /\ \A t \in (Smokers \ {s}): Offer'[t] = Offer[t]
        /\ Offer'[s] = Ingredients
    \/ Smoking' = {}
       /\ \E s \in Smokers: Offer'[s] \in SUBSET(Ingredients) /\ Cardinality(Offer'[s]) = 2

Spec == Init /\ [][Next]_<<Smoking, Offer>>

FairSpec == Spec /\ WF_next(<<Smoking, Offer>>)

AtMostOne == Cardinality(Smoking) <= 1

=============================================================================
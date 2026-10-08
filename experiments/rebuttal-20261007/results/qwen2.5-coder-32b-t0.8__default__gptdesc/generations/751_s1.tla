------------------------------- MODULE CigaretteSmokers -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Smokers, Ingredients
VARIABLES Smoking, Offer

Init == /\ Smoking = {s \in Smokers | FALSE}
        /\ Offer \in (SUBSET Ingredients) \ {Ingredients}

Next ==
    \/ /\ EX \E s \in Smokers: 
            /\ Offer = Ingredients \ {s}
            /\ Smoking' = {s}
            /\ Offer' \in (SUBSET Ingredients) \ {Ingredients}
       \/ /\ UNCHANGED Smoking
          /\ Offer' \in (SUBSET Ingredients) \ {Ingredients}

Spec == Init /\ [][Next]_<<Smoking, Offer>>

AtMostOne == Cardinality(Smoking) <= 1

FairSpec == Spec /\ WF_vars(Next)

=====================================================================================
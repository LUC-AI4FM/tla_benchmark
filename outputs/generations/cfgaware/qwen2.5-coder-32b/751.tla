------------------------------- MODULE CigaretteSmokers ------------------------------

CONSTANTS Smokers, Ingredients

ASSUME Smokers = {"smoker1", "smoker2", "smoker3"}
ASSUME Ingredients = {"paper", "tobacco", "matches"}

VARIABLES smoking, offer

TypeOK == /\ smoking \in [Smokers -> BOOLEAN]
          /\ offer \in SUBSET Ingredients
          /\ Cardinality(offer) = 2

Init == /\ smoking = [s \in Smokers |-> FALSE]
        /\ offer \in { {"paper", "tobacco"}, {"tobacco", "matches"}, {"matches", "paper"} }

Next ==
    \/ /\ \E s \in Smokers : smoking[s] 
       /\ \/ offer = {"paper", "tobacco"} /\ s = "smoker3"
          \/ offer = {"tobacco", "matches"} /\ s = "smoker1"
          \/ offer = {"matches", "paper"} /\ s = "smoker2"
       /\ smoking' = [s \in Smokers |-> FALSE]
       /\ offer' \in { {"paper", "tobacco"}, {"tobacco", "matches"}, {"matches", "paper"} }
    \/ /\ \A s \in Smokers : ~smoking[s] 
       /\ \E o \in { {"paper", "tobacco"}, {"tobacco", "matches"}, {"matches", "paper"} } :
            offer' = o
       /\ smoking' = [s \in Smokers |-> FALSE]

AtMostOne == Cardinality({s \in Smokers : smoking[s]}) <= 1

Spec == Init /\ [][Next]_<<smoking, offer>>

FairSpec == Spec /\ WF_next(<<smoking, offer>>)

=============================================================================
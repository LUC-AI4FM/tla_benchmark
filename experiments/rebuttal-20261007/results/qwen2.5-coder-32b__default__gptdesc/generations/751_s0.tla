------------------------------- MODULE CigaretteSmokers -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Smokers, Ingredients
ASSUME Smokers = {"smoker1", "smoker2", "smoker3"}
ASSUME Ingredients = {"paper", "tobacco", "matches"}
ASSUME \A s \in Smokers: (\E i \in Ingredients: i \notin {i \in Ingredients : s \in HasIngredient[i]})

VARIABLES smoking, offer

HasIngredient == [ "paper" |-> {"smoker1", "smoker2"},
                   "tobacco" |-> {"smoker2", "smoker3"},
                   "matches" |-> {"smoker3", "smoker1"} ]

Init == /\ smoking = {}
        /\ offer \in Ingredients

Next ==
    \/ /\ \E s \in Smokers: s \notin smoking
       /\ \E i \in Ingredients: i = offer /\ s \in HasIngredient[i]
       /\ smoking' = {s}
       /\ UNCHANGED offer
    \/ /\ smoking = {}
       /\ offer' \in Ingredients
       /\ UNCHANGED smoking

Spec == Init /\ [][Next]_<<smoking, offer>>

AtMostOne ==
    \/ smoking = {}
    \/ \E s \in Smokers: smoking = {s}

FairSpec == Spec /\ WF_next(<<smoking, offer>>)

=============================================================================
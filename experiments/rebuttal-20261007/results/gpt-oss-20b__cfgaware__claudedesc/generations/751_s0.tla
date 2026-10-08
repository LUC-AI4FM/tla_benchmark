------------------------------ MODULE CigaretteSmokers ------------------------------
CONSTANTS Ingredients, Offers

(* Record type for a smoker *)
Smoker == [smoking -> BOOLEAN]

VARIABLES smokers, dealer

Init ==
    /\ smokers = [i \in Ingredients |-> [smoking -> FALSE]]
    /\ dealer \in Offers

startSmoking ==
    /\ dealer \in Offers
    /\ LET missing == CHOOSE i \in Ingredients : i \notin dealer IN
       /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
       /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
    /\ EXISTS i \in Ingredients : smokers[i].smoking
    /\ LET smokingSmoker == CHOOSE i \in Ingredients : smokers[i].smoking IN
       /\ smokers' = [smokers EXCEPT ![smokingSmoker].smoking = FALSE]
       /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ []Next

TypeOK ==
    /\ smokers \in [Ingredients -> Smoker]
    /\ (dealer \in Offers \/ dealer = {})

AtMostOne ==
    LET smokingSet == {i \in Ingredients : smokers[i].smoking} IN
    #smokingSet <= 1

=============================================================================
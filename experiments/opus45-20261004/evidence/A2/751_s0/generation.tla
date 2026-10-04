---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

vars == <<smokers, dealer>>

TypeOK ==
    /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
    /\ dealer \in SUBSET Ingredients

AtMostOne ==
    Cardinality({i \in Ingredients : smokers[i].smoking}) <= 1

Init ==
    /\ smokers = [i \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

startSmoking ==
    /\ dealer \in Offers
    /\ \E i \in Ingredients :
        /\ dealer = Ingredients \ {i}
        /\ smokers' = [smokers EXCEPT ![i].smoking = TRUE]
        /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
    /\ \E i \in Ingredients :
        /\ smokers[i].smoking
        /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE]
        /\ \E offer \in Offers : dealer' = offer

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

=================================================================================
---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

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
        /\ smokers[i].smoking = TRUE
        /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

=============================================================================
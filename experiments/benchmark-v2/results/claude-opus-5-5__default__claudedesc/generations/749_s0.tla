---------------------------- MODULE MCCigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS matches, paper, tobacco

Ingredients == {matches, paper, tobacco}

Offers == { Ingredients \ {i} : i \in Ingredients }

ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smokers, dealer

vars == <<smokers, dealer>>

TypeOK ==
    /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
    /\ dealer \in Offers \cup {{}}

AtMostOne ==
    Cardinality({ r \in Ingredients : smokers[r].smoking }) <= 1

Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ \E r \in Ingredients :
        /\ {r} \cup dealer = Ingredients
        /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
        /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
        /\ smokers[r].smoking
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => [](TypeOK /\ AtMostOne)
=============================================================================
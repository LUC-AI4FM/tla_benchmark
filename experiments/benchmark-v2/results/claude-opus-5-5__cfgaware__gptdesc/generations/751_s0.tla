------------------------------ MODULE CigaretteSmokers ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |->
                                  [smoking |-> {r} = Ingredients \ dealer]]
                /\ dealer' = {}

stopSmoking == /\ dealer = {}
               /\ \E r \in Ingredients :
                     /\ smokers[r].smoking
                     /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=====================================================================================
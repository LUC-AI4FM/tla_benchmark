---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

vars == <<smokers, dealer>>

ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

TypeOK ==
    /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
    /\ dealer \in Offers \cup {{}}

Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                     [smoking |-> ({r} \cup dealer = Ingredients)]]
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

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

EventuallySmoke ==
    \A o \in Offers : (dealer = o) ~> (\E r \in Ingredients : smokers[r].smoking)
=============================================================================
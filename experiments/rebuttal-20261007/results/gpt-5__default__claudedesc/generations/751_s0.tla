----------------------------- MODULE CigaretteSmokers -----------------------------

EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

ASSUME Cardinality(Ingredients) = 3
ASSUME Offers = { Ingredients \ {i} : i \in Ingredients }

VARIABLES smokers, dealer

vars == << smokers, dealer >>

TypeOK ==
  /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
  /\ dealer \in SUBSET Ingredients
  /\ (dealer = {} \/ dealer \in Offers)

NoOneSmoking ==
  \A i \in Ingredients : ~smokers[i].smoking

AtMostOne ==
  \A i, j \in Ingredients :
    i # j => ~(smokers[i].smoking /\ smokers[j].smoking)

ExactlyOneSmoking ==
  \E i \in Ingredients :
    /\ smokers[i].smoking
    /\ \A j \in Ingredients : j # i => ~smokers[j].smoking

Init ==
  /\ smokers = [ i \in Ingredients |-> [ smoking |-> FALSE ] ]
  /\ dealer \in Offers

startSmoking ==
  /\ dealer # {}
  /\ dealer \in Offers
  /\ NoOneSmoking
  /\ LET i == CHOOSE k \in Ingredients : dealer = Ingredients \ {k}
     IN /\ smokers' = [smokers EXCEPT ![i].smoking = TRUE]
        /\ dealer'  = {}

stopSmoking ==
  /\ dealer = {}
  /\ ExactlyOneSmoking
  /\ LET i == CHOOSE k \in Ingredients : smokers[k].smoking
     IN /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE]
        /\ dealer'  \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)
================================================================================
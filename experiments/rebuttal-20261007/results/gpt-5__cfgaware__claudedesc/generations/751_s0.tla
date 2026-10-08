------------------------------ MODULE CigaretteSmokers ------------------------------

CONSTANTS
  Ingredients,
  Offers

VARIABLES
  smokers,
  dealer

vars == << smokers, dealer >>

Init ==
  /\ smokers = [ i \in Ingredients |-> [ smoking |-> FALSE ] ]
  /\ dealer \in Offers

startSmoking ==
  /\ dealer \in Offers
  /\ LET miss == CHOOSE j \in Ingredients : dealer = Ingredients \ {j}
     IN
        /\ smokers' = [smokers EXCEPT ![miss].smoking = TRUE]
        /\ dealer' = {}

stopSmoking ==
  /\ dealer = {}
  /\ \E j \in Ingredients : smokers[j].smoking
  /\ LET s == CHOOSE j \in Ingredients : smokers[j].smoking
     IN
        /\ smokers' = [smokers EXCEPT ![s].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

TypeOK ==
  /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
  /\ dealer \in Offers \cup { {} }
  /\ Offers \subseteq SUBSET Ingredients
  /\ \A o \in Offers : \E i \in Ingredients : o = Ingredients \ {i}

AtMostOne ==
  \A i, j \in Ingredients :
    i # j => ~(smokers[i].smoking /\ smokers[j].smoking)

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Spec /\ WF_vars(Next)

=============================================================================
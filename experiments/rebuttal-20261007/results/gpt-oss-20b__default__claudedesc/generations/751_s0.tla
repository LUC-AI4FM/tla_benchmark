------------------------------ MODULE CigaretteSmokers ------------------------------
EXTENDS TLC

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

(* Type definition *)
TypeOK ==
  /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
  /\ dealer \subseteq Ingredients
  /\ (dealer = {} \/ dealer \in Offers)

(* Invariant: at most one smoker smoking *)
AtMostOne ==
  LET cnt == |{i \in Ingredients : smokers[i].smoking}|
  IN cnt <= 1

Init ==
  /\ smokers = [i \in Ingredients |-> [smoking -> FALSE]]
  /\ dealer \in Offers

startSmoking ==
  /\ dealer \in Offers
  /\ LET missing == CHOOSE i \in Ingredients : i \notin dealer
     IN /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
        /\ dealer' = {}

stopSmoking ==
  /\ dealer = {}
  /\ LET smokingSet == {i \in Ingredients : smokers[i].smoking}
     IN /\ |smokingSet| = 1
        /\ LET i == CHOOSE j \in smokingSet : TRUE
           IN /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE]
              /\ dealer' = CHOOSE o \in Offers : TRUE

Next ==
  startSmoking \/ stopSmoking

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Spec /\ WF_vars(Next)

=============================================================================
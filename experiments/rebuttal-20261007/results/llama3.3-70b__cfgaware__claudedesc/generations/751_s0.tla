---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

TypeOK == 
  /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
  /\ dealer \in Offers \cup {<<>>}

AtMostOne == 
  /\ \E i \in Ingredients : smokers[i].smoking 
  => ~(\E j \in Ingredients \ {i} : smokers[j].smoking)

Init == 
  /\ smokers = [i \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer \in Offers

startSmoking(i \in Ingredients) == 
  /\ i \notin dealer
  /\ dealer \cup {i} = Ingredients
  /\ smokers' = [smokers EXCEPT ![i].smoking = TRUE]
  /\ dealer' = <<>>

stopSmoking(i \in Ingredients) == 
  /\ dealer = <<>>
  /\ smokers[i].smoking
  /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE]
  /\ dealer' \in Offers

Next == 
  (\E i \in Ingredients : startSmoking(i)) 
  \/ (\E i \in Ingredients : stopSmoking(i))

Spec == Init /\ [][Next]_<<smokers, dealer>>

FairSpec == Spec /\ WF_<<smokers, dealer>>(Next)

===============================================================================
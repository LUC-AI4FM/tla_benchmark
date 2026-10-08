---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers
VARIABLES dealerOffer, smoking

TypeOK == Ingredients \in SUBSET OF Strings /\ 
         Offers \in SUBSET OF SUBSET Ingredients /\ 
         \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1 /\ 
         smoking \in [Smokers -> {<<False, 0>>, <<True, 0>>}] /\ 
         dealerOffer \in Offers

AtMostOne == \A s1, s2 \in Smokers : 
             ~(smoking[s1] = <<True, 0>>) \/ ~(smoking[s2] = <<True, 0>>)

Spec == 
  Init /\ [][Next]_dealerOffer /\ WF_dealerOffer(Offers) /\ 
  \A s \in Smokers : WF_smoker(s)

Init == dealerOffer = {} /\ smoking = [s \in Smokers |-> <<False, 0>>]

Next == \E o \in Offers : 
        (dealerOffer = {} /\ dealerOffer' = o /\ UNCHANGED smoking) \/ 
        (\E s \in Smokers : 
          (smoking[s] = <<False, 0>> /\ Ingredients - dealerOffer = {i \in Ingredients : i = IngredientOf(s)} /\ 
           dealerOffer' = {} /\ smoking' = [smoking EXCEPT ![s] = <<True, 0>>]) \/ 
          (smoking[s] = <<True, 0>> /\ dealerOffer' = {} /\ smoking' = [smoking EXCEPT ![s] = <<False, 0>>]))

WF_dealerOffer(offers) == \A o \in offers : <>dealerOffer = o

WF_smoker(s) == <>smoking[s] = <<True, 0>>

IngredientOf(s) == 
  IF s = "Smoker1" THEN "matches"
  ELSE IF s = "Smoker2" THEN "paper"
  ELSE "tobacco"

Smokers == {"Smoker1", "Smoker2", "Smoker3"}
===============================================================================
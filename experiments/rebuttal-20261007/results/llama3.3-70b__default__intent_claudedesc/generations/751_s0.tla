```
MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers
VARIABLES dealerOffer, smokers, smoking

Init ==
  /\ dealerOffer \in Offers
  /\ smokers = [s \in {1, 2, 3} |-> FALSE]
  /\ smoking = FALSE

Next ==
  /\ IF smoking THEN
    /\ dealerOffer' = dealerOffer
    /\ smokers' = [smokers EXCEPT ![missingIngredient(dealerOffer)] = FALSE]
    /\ smoking' = FALSE
  ELSE
    /\ E s \in {1, 2, 3} :
      /\ missingIngredient(dealerOffer) = ingredient(s)
      /\ smokers' = [smokers EXCEPT ![s] = TRUE]
      /\ dealerOffer' = dealerOffer
      /\ smoking' = TRUE
    OR
    /\ dealerOffer' \in Offers
    /\ smokers' = smokers
    /\ smoking' = FALSE

Spec == Init /\ [][Next]_<<dealerOffer, smokers, smoking>>
  
Fairness == <>[]<>(smoking)

THEOREM Spec => []Fairness

missingIngredient(offer) ==
  CHOOSE i \in Ingredients : i \notin offer

ingredient(s) ==
  CASE s = 1 -> "matches"
  [] s = 2 -> "paper"
  [] s = 3 -> "tobacco"

SafetyInvariant == [](smokers = [s \in {1, 2, 3} |-> FALSE] \/ (Cardinality({s \in {1, 2, 3} : smokers[s]})) <= 1)
```
Note: The `THEOREM` statement is used to specify the liveness property that every offer eventually leads to a smoker smoking. However, proving this theorem requires additional tools and techniques beyond just writing the TLA+ specification.
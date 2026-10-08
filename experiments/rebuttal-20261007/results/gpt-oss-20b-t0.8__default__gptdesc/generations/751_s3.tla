```
\* -*- tla -*-

MODULE CigaretteSmokers
EXTENDS Naturals, TLC

CONSTANTS Ingredients, Smokers

VARIABLES dealerOffer, smoking

(* Helper predicate that characterizes a valid offer *)
OfferSet(s) == s ⊆ Ingredients /\ #s = 2

Init ==
   /\ OfferSet(dealerOffer)
   /\ DOMAIN(smoking) = Smokers
   /\ \A i ∈ Smokers : smoking[i] = FALSE

DealerAction ==
   /\ OfferSet(dealerOffer')
   /\ DOMAIN(smoking') = Smokers
   /\ \A i ∈ Smokers : smoking'[i] = FALSE

SmokerAction(i) ==
   /\ i ∈ Smokers
   /\ dealerOffer = Ingredients \ {i}
   /\ ~smoking[i]
   /\ DOMAIN(smoking') = Smokers
   /\ \A j ∈ Smokers :
        IF j = i THEN smoking'[j] = TRUE ELSE smoking'[j] = FALSE

Next == DealerAction \/ (\E i ∈ Smokers: SmokerAction(i))

vars == <<dealerOffer, smoking>>

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_Next(Next)

AtMostOne == # { i \in Smokers : smoking[i] } <= 1
```
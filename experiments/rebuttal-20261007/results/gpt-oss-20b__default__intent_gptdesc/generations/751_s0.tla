MODULE CigaretteSmokers

EXTENDS Naturals, Sequences, TLC

CONSTANTS Ingredients, NONE

SMOKERS == Ingredients

VARIABLES currentSmoker, offer

vars == <<currentSmoker, offer>>

TypeInv ==
  /\ currentSmoker \in SMOKERS \/ currentSmoker = NONE
  /\ (offer = NONE) \/ ((|offer| = |Ingredients|-1) /\ offer \subseteq Ingredients)
  /\ NONE \notin Ingredients

Init ==
  /\ currentSmoker = NONE
  /\ offer = NONE

DealerAction ==
  /\ currentSmoker = NONE
  /\ offer = NONE
  /\ \E i \in Ingredients :
       LET newOffer == Ingredients \ {i} IN
          /\ offer' = newOffer
          /\ currentSmoker' = NONE

StartSmoker(s) ==
  /\ s \in SMOKERS
  /\ currentSmoker = NONE
  /\ offer = Ingredients \ {s}
  /\ currentSmoker' = s
  /\ offer' = NONE

FinishSmoker(s) ==
  /\ s \in SMOKERS
  /\ currentSmoker = s
  /\ currentSmoker' = NONE
  /\ offer' = NONE

Next == DealerAction \/ \E s \in SMOKERS : StartSmoker(s) \/ \E s \in SMOKERS : FinishSmoker(s)

SafetyInv == TypeInv

LivenessOfferConsumed ==
  []( (offer != NONE /\ \E s \in SMOKERS : offer = Ingredients \ {s}) => <> (currentSmoker = s) )

ProgressOffers ==
  []<>(currentSmoker = NONE /\ offer != NONE)

Spec == Init /\ [][Next]_vars /\ SafetyInv /\ LivenessOfferConsumed /\ ProgressOffers

END MODULE
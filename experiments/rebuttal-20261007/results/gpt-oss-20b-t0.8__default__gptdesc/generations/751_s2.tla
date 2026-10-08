MODULE CigaretteSmokers

CONSTANTS Ingredients

VARIABLES smoke, offer

OfferSet == {
    Ingredients \ {"tobacco"},
    Ingredients \ {"paper"},
    Ingredients \ {"matches"}
}

Missing(o) == Ingredients \ o

Init ==
   /\ smoke = {}
   /\ offer \in OfferSet

DealerOffer ==
   /\ smoke = {}
   /\ CHOOSE o \in OfferSet :
        (offer' = o
         /\ smoke' = {})

SmokerStart ==
   /\ smoke = {}
   /\ ∃ m \in Ingredients :
        (Missing(offer) = {m}
         /\ smoke' = {m}
         /\ offer' = offer)

SmokerStop ==
   /\ smoke /= {}
   /\ smoke' = {}
   /\ offer' = offer

Next == DealerOffer \/ SmokerStart \/ SmokerStop

AtMostOne == ~ (∃ s1 ∈ smoke, s2 ∈ smoke : s1 /= s2)

Fairness == WF_∃(Next)

vars == <<smoke, offer>>

Spec == Init /\ [][Next]_{vars} /\ []AtMostOne /\ Fairness
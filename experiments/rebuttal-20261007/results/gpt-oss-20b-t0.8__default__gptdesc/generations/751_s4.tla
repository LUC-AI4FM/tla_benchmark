MODULE Smokers
EXTENDS Naturals

CONSTANTS T, P, M

VARIABLE dealerOffer, smoking

SmokerIds == 1..3

INGREDIENTS == {T, P, M}

SmokerIngredient == [1 -> T, 2 -> P, 3 -> M]

OfferSet == { s \subseteq INGREDIENTS : #(s) = 2 }

AtMostOneSmoking ==
   LET ss := { sm ∈ SmokerIds : smoking[sm] } IN #(ss) <= 1

Init ==
   /\ dealerOffer ∈ OfferSet
   /\ smoking == [ sm ∈ SmokerIds |-> FALSE ]

Deal ==
   /\ ~AtMostOneSmoking
   /\ UNCHANGED <<smoking>>
   /\ dealerOffer' ∈ OfferSet

StartSmoke(sm) ==
   /\ sm ∈ SmokerIds
   /\ smoking[sm] = FALSE
   /\ dealerOffer = INGREDIENTS \ { SmokerIngredient[sm] }
   /\ smoking'[sm] = TRUE
   /\ UNCHANGED <<dealerOffer>>

EndSmoke(sm) ==
   /\ sm ∈ SmokerIds
   /\ smoking[sm] = TRUE
   /\ smoking'[sm] = FALSE
   /\ UNCHANGED <<dealerOffer>>

Next ==
   Deal \/ ∃ sm ∈ SmokerIds : (StartSmoke(sm) \/ EndSmoke(sm))

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)
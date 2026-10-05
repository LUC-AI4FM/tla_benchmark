---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients

VARIABLES offer, smoking, dealerReady

vars == <<offer, smoking, dealerReady>>

\* Type invariant ensuring offers are valid subsets and smoking states are well-formed
TypeOK ==
    /\ offer \subseteq Ingredients
    /\ smoking \subseteq Ingredients
    /\ dealerReady \in BOOLEAN

\* Safety property: at most one smoker may be smoking at any given time
AtMostOne == Cardinality(smoking) <= 1

\* The set of valid offers (subsets missing exactly one ingredient)
ValidOffers == {Ingredients \ {i} : i \in Ingredients}

\* A smoker with ingredient i can smoke when the offer contains all other ingredients
CanSmoke(i) == offer = Ingredients \ {i}

\* Initial state: no offer on table, no one smoking, dealer ready to make offer
Init ==
    /\ offer = {}
    /\ smoking = {}
    /\ dealerReady = TRUE

\* Dealer places an offer (a set missing exactly one ingredient)
DealerOffer ==
    /\ dealerReady = TRUE
    /\ smoking = {}
    /\ \E validOffer \in ValidOffers :
        /\ offer' = validOffer
        /\ dealerReady' = FALSE
        /\ UNCHANGED smoking

\* Smoker with ingredient i takes the offer and starts smoking
SmokerTake(i) ==
    /\ i \in Ingredients
    /\ CanSmoke(i)
    /\ smoking = {}
    /\ smoking' = {i}
    /\ offer' = {}
    /\ UNCHANGED dealerReady

\* Smoker with ingredient i finishes smoking
SmokerFinish(i) ==
    /\ i \in smoking
    /\ smoking' = {}
    /\ dealerReady' = TRUE
    /\ UNCHANGED offer

\* Next state relation
Next ==
    \/ DealerOffer
    \/ \E i \in Ingredients : SmokerTake(i)
    \/ \E i \in Ingredients : SmokerFinish(i)

\* Fairness conditions
Fairness ==
    /\ WF_vars(DealerOffer)
    /\ \A i \in Ingredients : WF_vars(SmokerTake(i))
    /\ \A i \in Ingredients : WF_vars(SmokerFinish(i))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* An offer enables some smoker
OfferEnablesSmoker == \E i \in Ingredients : CanSmoke(i)

\* Liveness: if an offer enables some smoker, eventually some smoker starts smoking
Liveness == [](offer # {} => <>(smoking # {}))

\* Progress of offers: the dealer eventually places offers repeatedly
ProgressOfOffers == []<>(offer # {})

\* Domain invariant: offers are always valid (either empty or missing exactly one ingredient)
DomainInvariant ==
    \/ offer = {}
    \/ offer \in ValidOffers

\* Combined invariant
Invariant == TypeOK /\ AtMostOne /\ DomainInvariant

=============================================================================
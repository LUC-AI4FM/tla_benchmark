---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients

ASSUME Cardinality(Ingredients) >= 2

VARIABLES
    offer,          \* The current offer on the table (a set of ingredients or "none")
    smoking,        \* The smoker currently smoking (an ingredient or "none")
    smokerReady     \* Whether a smoker has finished and dealer can place new offer

vars == <<offer, smoking, smokerReady>>

\* Each smoker is identified by the ingredient they possess
Smokers == Ingredients

\* Valid offers are subsets of Ingredients missing exactly one ingredient
ValidOffers == {s \in SUBSET Ingredients : Cardinality(s) = Cardinality(Ingredients) - 1}

\* The ingredient a smoker needs is everything except what they have
IngredientsNeeded(smoker) == Ingredients \ {smoker}

\* A smoker can take an offer if the offer contains exactly the ingredients they need
CanSmoke(smoker) == offer = IngredientsNeeded(smoker)

TypeInvariant ==
    /\ offer \in ValidOffers \cup {"none"}
    /\ smoking \in Smokers \cup {"none"}
    /\ smokerReady \in BOOLEAN

\* Domain invariant: offers are always valid subsets missing exactly one ingredient
OfferDomainInvariant ==
    offer /= "none" => offer \in ValidOffers

\* Smoking states are well-formed
SmokingWellFormed ==
    /\ smoking \in Smokers \cup {"none"}
    /\ (smoking /= "none") => (offer = "none")

Init ==
    /\ offer = "none"
    /\ smoking = "none"
    /\ smokerReady = TRUE

\* Dealer places an offer when no one is smoking and smoker is ready
DealerOffer ==
    /\ offer = "none"
    /\ smoking = "none"
    /\ smokerReady = TRUE
    /\ \E newOffer \in ValidOffers :
        /\ offer' = newOffer
        /\ smokerReady' = FALSE
    /\ UNCHANGED smoking

\* A smoker takes the offer and starts smoking
SmokerTake(smoker) ==
    /\ offer /= "none"
    /\ smoking = "none"
    /\ CanSmoke(smoker)
    /\ smoking' = smoker
    /\ offer' = "none"
    /\ UNCHANGED smokerReady

\* A smoker finishes smoking
SmokerFinish(smoker) ==
    /\ smoking = smoker
    /\ smoking' = "none"
    /\ smokerReady' = TRUE
    /\ UNCHANGED offer

Next ==
    \/ DealerOffer
    \/ \E s \in Smokers : SmokerTake(s)
    \/ \E s \in Smokers : SmokerFinish(s)

\* Fairness: weak fairness on all actions to ensure progress
Fairness ==
    /\ WF_vars(DealerOffer)
    /\ \A s \in Smokers : WF_vars(SmokerTake(s))
    /\ \A s \in Smokers : WF_vars(SmokerFinish(s))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: at most one smoker may be smoking at any given time
\* Since smoking is a single value (not a set), this is inherently satisfied
\* but we express it explicitly
AtMostOneSmoking ==
    smoking \in Smokers \cup {"none"}

SafetyInvariant == AtMostOneSmoking

\* Combined type and domain invariants
Invariants ==
    /\ TypeInvariant
    /\ OfferDomainInvariant
    /\ SmokingWellFormed
    /\ SafetyInvariant

\* Liveness: if an offer enables some smoker, eventually some smoker starts smoking
\* An offer enables smoker s if offer = IngredientsNeeded(s)
OfferEnablesSomeSmoker == \E s \in Smokers : CanSmoke(s)
SomeSmokerSmoking == smoking /= "none"

OfferEventuallyTaken ==
    (offer /= "none" /\ OfferEnablesSomeSmoker) ~> SomeSmokerSmoking

\* Progress of offers: the dealer eventually places offers repeatedly
\* Expressed as: it's always the case that eventually an offer will be placed
ProgressOfOffers ==
    []<>(offer /= "none" \/ smoking /= "none")

\* Alternative: from any state, eventually an offer gets placed
DealerMakesProgress ==
    [](smokerReady /\ smoking = "none" /\ offer = "none" => <>(offer /= "none"))

\* The system does not deadlock
NoDeadlock ==
    [](ENABLED Next)

\* Combined liveness properties
LivenessProperties ==
    /\ OfferEventuallyTaken
    /\ ProgressOfOffers
    /\ DealerMakesProgress

=============================================================================
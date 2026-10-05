---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

ASSUME IngredientsAssumption == Ingredients # {}
ASSUME OffersAssumption == Offers # {} /\ Offers \subseteq SUBSET Ingredients
ASSUME OfferSizeAssumption == \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES
    table,      \* The set of ingredients currently on the table (or empty)
    smoking,    \* The ingredient of the smoker currently smoking (or "none")
    dealer_turn \* TRUE if it's the dealer's turn to place ingredients

vars == <<table, smoking, dealer_turn>>

Smokers == Ingredients

Complement(offer) == Ingredients \ offer

TypeOK ==
    /\ table \in SUBSET Ingredients
    /\ (smoking = "none" \/ smoking \in Smokers)
    /\ dealer_turn \in BOOLEAN

Init ==
    /\ table = {}
    /\ smoking = "none"
    /\ dealer_turn = TRUE

DealerPlacesOffer(offer) ==
    /\ dealer_turn = TRUE
    /\ smoking = "none"
    /\ table = {}
    /\ offer \in Offers
    /\ table' = offer
    /\ dealer_turn' = FALSE
    /\ UNCHANGED smoking

SmokerStartsSmoking(smoker) ==
    /\ dealer_turn = FALSE
    /\ smoking = "none"
    /\ table # {}
    /\ smoker = CHOOSE i \in Ingredients : i \in Complement(table)
    /\ smoking' = smoker
    /\ table' = {}
    /\ UNCHANGED dealer_turn

SmokerFinishesSmoking(smoker) ==
    /\ smoking = smoker
    /\ smoking' = "none"
    /\ dealer_turn' = TRUE
    /\ UNCHANGED table

DealerAction == \E offer \in Offers : DealerPlacesOffer(offer)

SmokerStartsAction == \E smoker \in Smokers : SmokerStartsSmoking(smoker)

SmokerFinishesAction == \E smoker \in Smokers : SmokerFinishesSmoking(smoker)

Next ==
    \/ DealerAction
    \/ SmokerStartsAction
    \/ SmokerFinishesAction

MutualExclusion ==
    smoking = "none" \/ \E s \in Smokers : smoking = s

AtMostOneSmoking ==
    Cardinality({s \in Smokers : smoking = s}) <= 1

SafetyInvariant == MutualExclusion /\ AtMostOneSmoking

Fairness ==
    /\ WF_vars(DealerAction)
    /\ WF_vars(SmokerStartsAction)
    /\ WF_vars(SmokerFinishesAction)

Spec == Init /\ [][Next]_vars /\ Fairness

OfferLeadsToSmoking ==
    \A offer \in Offers : 
        table = offer ~> smoking # "none"

NoDeadlock ==
    [](smoking # "none" \/ table # {} \/ dealer_turn)

Progress ==
    []<>(smoking # "none")

EventuallySmokes ==
    \A s \in Smokers : []<>(smoking = s)

=============================================================================
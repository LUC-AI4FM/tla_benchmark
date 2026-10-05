---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

ASSUME /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smoking, offer

vars == <<smoking, offer>>

Smokers == Ingredients

MissingIngredient(o) == CHOOSE i \in Ingredients : i \notin o

Init ==
    /\ smoking = [s \in Smokers |-> FALSE]
    /\ offer = {}

DealerOffer(o) ==
    /\ offer = {}
    /\ \A s \in Smokers : smoking[s] = FALSE
    /\ o \in Offers
    /\ offer' = o
    /\ smoking' = smoking

SmokerSmoke(s) ==
    /\ offer # {}
    /\ s = MissingIngredient(offer)
    /\ smoking[s] = FALSE
    /\ smoking' = [smoking EXCEPT ![s] = TRUE]
    /\ offer' = offer

SmokerFinish(s) ==
    /\ smoking[s] = TRUE
    /\ smoking' = [smoking EXCEPT ![s] = FALSE]
    /\ offer' = {}

Next ==
    \/ \E o \in Offers : DealerOffer(o)
    \/ \E s \in Smokers : SmokerSmoke(s)
    \/ \E s \in Smokers : SmokerFinish(s)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne ==
    Cardinality({s \in Smokers : smoking[s] = TRUE}) <= 1

TypeInvariant ==
    /\ smoking \in [Smokers -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

=============================================================================
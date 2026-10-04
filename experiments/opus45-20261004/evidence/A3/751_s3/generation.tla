---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* Structural constraint: each offer is missing exactly one ingredient
ASSUME \A o \in Offers : o \subseteq Ingredients /\ Cardinality(Ingredients \ o) = 1

\* The smokers are identified by the ingredient they have (the one missing from an offer)
Smokers == Ingredients

\* Get the smoker who has the missing ingredient for a given offer
SmokerForOffer(o) == CHOOSE i \in Ingredients : i \notin o

Init ==
    /\ smoking = [s \in Smokers |-> FALSE]
    /\ offer = {}

\* Dealer makes an offer (when no offer is currently on the table)
DealerOffer ==
    /\ offer = {}
    /\ \E o \in Offers : offer' = o
    /\ UNCHANGED smoking

\* Smoker with the missing ingredient picks up the offer and starts smoking
SmokerPickUp ==
    /\ offer /= {}
    /\ LET s == SmokerForOffer(offer)
       IN /\ smoking' = [smoking EXCEPT ![s] = TRUE]
          /\ offer' = {}

\* Smoker finishes smoking
SmokerFinish ==
    /\ \E s \in Smokers : smoking[s]
    /\ \E s \in Smokers : 
        /\ smoking[s]
        /\ smoking' = [smoking EXCEPT ![s] = FALSE]
    /\ UNCHANGED offer

Next ==
    \/ DealerOffer
    \/ SmokerPickUp
    \/ SmokerFinish

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

\* Safety invariant: at most one smoker is smoking at any time
AtMostOne == Cardinality({s \in Smokers : smoking[s]}) <= 1

\* Type invariant for completeness
TypeOK ==
    /\ smoking \in [Smokers -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients)

=============================================================================
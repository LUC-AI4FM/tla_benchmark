---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers, Smokers

VARIABLES smoking, offer

vars == <<smoking, offer>>

ASSUME /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1
       /\ Smokers = Ingredients

TypeOK == /\ smoking \in [Smokers -> BOOLEAN]
          /\ offer \in Offers \cup {{}}}

MissingIngredient(o) == CHOOSE i \in Ingredients : i \notin o

Init == /\ smoking = [s \in Smokers |-> FALSE]
        /\ offer = {}

DealerOffer == /\ offer = {}
               /\ \E o \in Offers : offer' = o
               /\ smoking' = smoking

SmokerSmoke(s) == /\ offer # {}
                  /\ s = MissingIngredient(offer)
                  /\ smoking' = [smoking EXCEPT ![s] = TRUE]
                  /\ offer' = offer

SmokerFinish(s) == /\ smoking[s] = TRUE
                   /\ smoking' = [smoking EXCEPT ![s] = FALSE]
                   /\ offer' = {}

Next == \/ DealerOffer
        \/ \E s \in Smokers : SmokerSmoke(s)
        \/ \E s \in Smokers : SmokerFinish(s)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({s \in Smokers : smoking[s]}) <= 1

=============================================================================
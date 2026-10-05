---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

ASSUME /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

MissingIngredient(o) == Ingredients \ o

TypeOK == /\ smoking \in [Ingredients -> BOOLEAN]
          /\ offer \in Offers \cup {{}

Init == /\ smoking = [i \in Ingredients |-> FALSE]
        /\ offer = {}

DealerOffer(o) == /\ offer = {}
                  /\ o \in Offers
                  /\ offer' = o
                  /\ smoking' = smoking

Smoke(i) == /\ offer # {}
            /\ MissingIngredient(offer) = {i}
            /\ smoking' = [smoking EXCEPT ![i] = TRUE]
            /\ offer' = offer

FinishSmoking(i) == /\ smoking[i] = TRUE
                    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
                    /\ offer' = {}

Next == \/ \E o \in Offers : DealerOffer(o)
        \/ \E i \in Ingredients : Smoke(i)
        \/ \E i \in Ingredients : FinishSmoking(i)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

=============================================================================
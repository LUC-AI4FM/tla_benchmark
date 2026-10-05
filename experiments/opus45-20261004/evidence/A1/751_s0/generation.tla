---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

----------------------------------------------------------------------------

ASSUME /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

----------------------------------------------------------------------------

MissingIngredient(o) == CHOOSE i \in Ingredients : i \notin o

TypeOK == /\ smoking \in [Ingredients -> BOOLEAN]
          /\ offer \in Offers \cup {{}}}

Init == /\ smoking = [i \in Ingredients |-> FALSE]
        /\ offer = {}

DealerOffer == /\ offer = {}
               /\ \E o \in Offers : offer' = o
               /\ smoking' = smoking

SmokerSmokes == /\ offer # {}
                /\ LET missing == MissingIngredient(offer)
                   IN /\ smoking' = [smoking EXCEPT ![missing] = TRUE]
                      /\ offer' = offer

SmokerFinishes == /\ \E i \in Ingredients : smoking[i] = TRUE
                  /\ smoking' = [i \in Ingredients |-> FALSE]
                  /\ offer' = {}

Next == DealerOffer \/ SmokerSmokes \/ SmokerFinishes

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------------------------

AtMostOne == Cardinality({i \in Ingredients : smoking[i] = TRUE}) <= 1

=============================================================================
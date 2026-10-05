---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Smokers, Ingredients, Offers

ASSUME /\ Smokers # {}
       /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A offer \in Offers : Cardinality(offer) = Cardinality(Ingredients) - 1

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK == /\ smoking \in [Smokers -> BOOLEAN]
          /\ offer \in Offers \cup {<<>>}

Init == /\ smoking = [s \in Smokers |-> FALSE]
        /\ offer = <<>>

DealerOffer == /\ offer = <<>>
               /\ \E o \in Offers : offer' = o
               /\ smoking' = smoking

SmokerSmoke(s) == /\ offer # <<>>
                  /\ smoking[s] = FALSE
                  /\ smoking' = [smoking EXCEPT ![s] = TRUE]
                  /\ offer' = offer

SmokerFinish(s) == /\ smoking[s] = TRUE
                   /\ smoking' = [smoking EXCEPT ![s] = FALSE]
                   /\ offer' = <<>>

Next == \/ DealerOffer
        \/ \E s \in Smokers : SmokerSmoke(s)
        \/ \E s \in Smokers : SmokerFinish(s)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({s \in Smokers : smoking[s]}) <= 1

=============================================================================
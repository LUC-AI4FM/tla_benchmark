---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

ASSUME /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A offer \in Offers : Cardinality(Ingredients \ offer) = 1

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK == /\ smoking \in [Ingredients -> BOOLEAN]
          /\ offer \in Offers \union {{}}}

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

smoker(ingredient) == Ingredients \ {ingredient}

Init == /\ smoking = [i \in Ingredients |-> FALSE]
        /\ offer = {}

DealerOffer == /\ offer = {}
               /\ \E o \in Offers : offer' = o
               /\ smoking' = smoking

SmokerSmoke(i) == /\ offer = smoker(i)
                  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
                  /\ offer' = offer

SmokerFinish(i) == /\ smoking[i] = TRUE
                   /\ smoking' = [smoking EXCEPT ![i] = FALSE]
                   /\ offer' = {}

Next == \/ DealerOffer
        \/ \E i \in Ingredients : SmokerSmoke(i)
        \/ \E i \in Ingredients : SmokerFinish(i)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

=============================================================================
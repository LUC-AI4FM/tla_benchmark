---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

vars == <<smokers, dealer>>

IngredientsVal == {"matches", "paper", "tobacco"}

OffersVal == { IngredientsVal \ {i} : i \in IngredientsVal }

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

Complement(o) == CHOOSE r \in Ingredients : {r} = Ingredients \ o

TypeOK ==
    /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
    /\ dealer \in Offers \cup {{}}

Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

StartSmoking ==
    /\ dealer # {}
    /\ \A r \in Ingredients : ~smokers[r].smoking
    /\ \E r \in Ingredients :
          /\ {r} = Ingredients \ dealer
          /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
    /\ dealer' = {}

StopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(StartSmoking)
        /\ WF_vars(StopSmoking)

\* ------------------------- Safety properties -------------------------

AtMostOne ==
    Cardinality({ r \in Ingredients : smokers[r].smoking }) <= 1

TableInvariant ==
    \/ dealer = {}
    \/ /\ dealer \in Offers
       /\ Cardinality(dealer) = Cardinality(Ingredients) - 1

ExclusiveAccess ==
    /\ (\E r \in Ingredients : smokers[r].smoking) => dealer = {}
    /\ dealer # {} => \A r \in Ingredients : ~smokers[r].smoking

TableFaithful ==
    dealer = {} <=> (\E r \in Ingredients : smokers[r].smoking)

SmokeOnlyAfterComplement ==
    [][\A r \in Ingredients :
          (~smokers[r].smoking /\ smokers'[r].smoking)
              => (dealer = Ingredients \ {r} /\ dealer' = {})]_vars

NoLossOrDuplication ==
    [][ /\ (dealer # {} /\ dealer' # dealer) => dealer' = {}
        /\ (dealer = {} /\ dealer' # {}) => dealer' \in Offers ]_vars

\* ------------------------- Liveness properties -------------------------

DealConsumed ==
    \A o \in Offers :
        (dealer = o) ~> (smokers[Complement(o)].smoking)

DealerProgress == []<>(dealer # {})

NoStarvation == (dealer # {}) ~> (dealer = {})

=============================================================================
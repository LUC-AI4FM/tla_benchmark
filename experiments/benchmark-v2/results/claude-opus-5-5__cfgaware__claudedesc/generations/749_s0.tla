---- MODULE MC_CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANTS
  \* @type: Set(Str);
  Ingredients,
  \* @type: Set(Set(Str));
  Offers

VARIABLES
  \* @type: Str -> [smoking: Bool];
  smokers,
  \* @type: Set(Str);
  dealer

\* @type: Set(Str);
IngredientsVal == {"matches", "paper", "tobacco"}

\* @type: Set(Set(Str));
OffersVal == { IngredientsVal \ {i} : i \in IngredientsVal }

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |->
                                 [smoking |-> ({r} \cup dealer) = Ingredients]]
                /\ dealer' = {}

stopSmoking == /\ dealer = {}
               /\ \E r \in Ingredients :
                     /\ smokers[r].smoking
                     /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====
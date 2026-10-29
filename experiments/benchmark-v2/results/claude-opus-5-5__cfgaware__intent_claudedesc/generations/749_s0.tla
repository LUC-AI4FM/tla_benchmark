---------------------------- MODULE CigaretteSmokers ----------------------------
(***************************************************************************)
(* The Cigarette Smokers Problem.                                          *)
(* A dealer repeatedly places two of three ingredients on the table. The   *)
(* smoker holding the complementary ingredient takes them, smokes, and     *)
(* when finished the dealer offers a new combination.                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

vars == <<smokers, dealer>>

(* Concrete values used by the model-checking configuration. *)
IngredientsVal == {"matches", "paper", "tobacco"}
OffersVal == { IngredientsVal \ {i} : i \in IngredientsVal }

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* The smoker with the complementary ingredient picks up the offer. *)
StartSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                      [smoking |-> ({r} \cup dealer) = Ingredients]]
    /\ dealer' = {}

(* The smoker finishes and the dealer offers a new combination. *)
StopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients : smokers[r].smoking
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

Progress == \A r \in Ingredients :
               (dealer = Ingredients \ {r}) ~> smokers[r].smoking
=============================================================================
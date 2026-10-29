------------------------- MODULE CigaretteSmokers -------------------------
(***************************************************************************)
(* The classic cigarette smokers synchronization problem.                  *)
(* A dealer repeatedly places on the table an offer: a set of ingredients  *)
(* that is missing exactly one ingredient. The smoker who holds the        *)
(* missing ingredient takes the offer and smokes. When that smoker         *)
(* finishes, the dealer may make a new offer.                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

(***************************************************************************)
(* Structural constraints on the possible offers: each offer is a subset   *)
(* of the ingredients that lacks exactly one ingredient.                   *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

(* The unique element of S satisfying P. *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* The smoker holding the missing ingredient takes the offer and smokes. *)
startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |->
                                 [smoking |-> {r} \cup dealer = Ingredients]]
                /\ dealer' = {}

(* The smoker finishes, and the dealer makes a new offer. *)
stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Safety: no more than one smoker is smoking at any time.                 *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================
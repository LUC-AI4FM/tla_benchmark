---------------------------- MODULE CigaretteSmokers ----------------------------
(***************************************************************************)
(* A specification of the Cigarette Smokers Problem (Patil, 1971).         *)
(* A dealer places two of three ingredients on the table. Each smoker has  *)
(* an infinite supply of exactly one ingredient. The smoker who has the    *)
(* missing ingredient takes the offer and smokes.                          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

(***************************************************************************)
(* Choose the unique element of S that satisfies P.                       *)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |->
                                 [smoking |-> {r} \cup dealer = Ingredients]]
                /\ dealer' = {}

stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
                  IN  smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================
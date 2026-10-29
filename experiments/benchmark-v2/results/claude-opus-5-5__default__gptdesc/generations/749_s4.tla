---------------------------- MODULE MC_CigaretteSmokersTyped ----------------------------
(***************************************************************************)
(* Apalache-oriented typed instance of the CigaretteSmokers specification. *)
(* It declares typed constants and variables and provides concrete         *)
(* model-value sets for use from configuration: a three-element            *)
(* ingredient universe and the induced set of two-ingredient offers.       *)
(*                                                                         *)
(* The original module would contain only `INSTANCE CigaretteSmokers`.     *)
(* So that this module parses on its own, the definitions of               *)
(* CigaretteSmokers are inlined below, with no substitutions.              *)
(***************************************************************************)
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

(***************************************************************************)
(* Concrete helper definitions intended for use from configuration.       *)
(***************************************************************************)
\* @type: Set(Str);
IngredientsVal == {"matches_OF_INGREDIENT", "paper_OF_INGREDIENT", "tobacco_OF_INGREDIENT"}

\* @type: Set(Set(Str));
OffersVal == { IngredientsVal \ {i} : i \in IngredientsVal }

(***************************************************************************)
(* Inlined contents of CigaretteSmokers (instantiated without             *)
(* substitutions).                                                         *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                      [smoking |-> {r} \cup dealer = Ingredients]]
    /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Safety: at most one smoker smokes at any time.                         *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

(***************************************************************************)
(* Liveness: eventually some smoker smokes (under FairSpec).              *)
(***************************************************************************)
Progress == <>(\E r \in Ingredients : smokers[r].smoking)

THEOREM Spec => [](TypeOK /\ AtMostOne)
THEOREM FairSpec => Progress
=============================================================================
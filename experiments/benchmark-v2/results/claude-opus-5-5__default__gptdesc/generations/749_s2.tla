------------------------- MODULE APACigaretteSmokers -------------------------
(***************************************************************************)
(* Apalache-oriented typed instance of the CigaretteSmokers specification. *)
(* Constants and variables carry Apalache type annotations, and concrete   *)
(* helper sets are provided for use from a model configuration:            *)
(*   ConstIngredients - a three-element ingredient universe                *)
(*   ConstOffers      - the induced set of two-ingredient offers           *)
(*                                                                         *)
(* In the original layout this module simply writes                        *)
(*      INSTANCE CigaretteSmokers                                          *)
(* without substitutions.  So that the module parses on its own with       *)
(* SANY, the definitions of the instantiated CigaretteSmokers module are   *)
(* reproduced inline below, under the same names.                          *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals

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
(* Concrete model values intended for use from the configuration file.     *)
(***************************************************************************)
ConstIngredients == {"matches", "paper", "tobacco"}

ConstOffers == {I \in SUBSET ConstIngredients : Cardinality(I) = 2}

(***************************************************************************)
(* Contents of the instantiated CigaretteSmokers module.                   *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers \in [Ingredients -> [smoking : {FALSE}]]
        /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                      [smoking |-> {r} \cup dealer = Ingredients]]
    /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN  smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================
------------------------- MODULE APACigaretteSmokers -------------------------
(***************************************************************************)
(* Apalache-oriented typed wrapper for the CigaretteSmokers specification. *)
(* It declares typed constants and variables, instantiates the            *)
(* CigaretteSmokers module without substitutions, and provides concrete   *)
(* model-value sets for use from a configuration: a three-element        *)
(* ingredient universe and the induced set of two-ingredient offers.      *)
(***************************************************************************)

CONSTANTS
    \* @type: Set(INGREDIENT);
    Ingredients,
    \* @type: Set(Set(INGREDIENT));
    Offers

VARIABLES
    \* @type: INGREDIENT -> [smoking: Bool];
    smokers,
    \* @type: Set(INGREDIENT);
    dealer

\* Instantiate the original specification without any substitutions.
CS == INSTANCE CigaretteSmokers

\* The transition system is the one defined by CigaretteSmokers.
Init == CS!Init
Next == CS!Next
Spec == CS!Spec

(***************************************************************************)
(* Concrete helper definitions intended for use from the configuration.   *)
(***************************************************************************)

\* A three-element ingredient universe, as Apalache model values.
\* @type: Set(INGREDIENT);
IngredientsInit ==
    { "matches_OF_INGREDIENT",
      "paper_OF_INGREDIENT",
      "tobacco_OF_INGREDIENT" }

\* The induced set of offers: every two-element subset of the ingredients.
\* @type: Set(Set(INGREDIENT));
OffersInit ==
    { IngredientsInit \ {i} : i \in IngredientsInit }

\* Constant initialization predicate for Apalache (--cinit).
ConstInit ==
    /\ Ingredients = IngredientsInit
    /\ Offers = OffersInit

=============================================================================
------------------------- MODULE APCigaretteSmokers -------------------------
(***************************************************************************)
(* Apalache-oriented type annotations and concrete helper definitions for  *)
(* an instance of the CigaretteSmokers specification.                      *)
(*                                                                         *)
(* This module does not define its own transition system.  The             *)
(* definitions Init, Next and Spec, together with every action, invariant *)
(* and temporal property, come from the CigaretteSmokers module through    *)
(* the unnamed INSTANCE below.  Defining them again here would make SANY   *)
(* report a multiple-definition error.                                     *)
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
(* Instantiate the algorithm without substitutions.  The constants and     *)
(* variables above are bound by name.                                      *)
(***************************************************************************)
INSTANCE CigaretteSmokers

(***************************************************************************)
(* Concrete model values for use from a configuration file.                *)
(***************************************************************************)

\* The three-element ingredient universe.
\* @type: Set(Str);
IngredientsVal == {"matches", "paper", "tobacco"}

\* The induced set of offers: every two-ingredient subset of the universe.
\* @type: Set(Set(Str));
OffersVal == { S \in SUBSET IngredientsVal : Cardinality(S) = 2 }

\* Apalache-style constant initializer (usable via --cinit=CInit).
CInit ==
    /\ Ingredients = IngredientsVal
    /\ Offers = OffersVal

=============================================================================
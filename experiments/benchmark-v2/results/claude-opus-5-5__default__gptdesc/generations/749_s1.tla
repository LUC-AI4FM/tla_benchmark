------------------------- MODULE APACigaretteSmokers -------------------------
(***************************************************************************)
(* Apalache-oriented typed instance of the CigaretteSmokers specification. *)
(* The transition system (Init, Next, Spec) and the properties of the      *)
(* algorithm are imported unchanged from the CigaretteSmokers module.      *)
(* This module only adds type annotations and concrete constant values.   *)
(***************************************************************************)

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

\* Imports Init, Next, Spec, invariants and properties of the algorithm.
INSTANCE CigaretteSmokers

(***************************************************************************)
(* Concrete model values, intended for use from configuration via         *)
(* constant substitution (e.g. Ingredients <- ingredients).               *)
(***************************************************************************)

\* The three-element ingredient universe.
\* @type: Set(Str);
ingredients == {"matches", "paper", "tobacco"}

\* The induced set of two-ingredient offers.
\* @type: Set(Set(Str));
offers == { {"matches", "paper"},
            {"matches", "tobacco"},
            {"paper", "tobacco"} }

=============================================================================
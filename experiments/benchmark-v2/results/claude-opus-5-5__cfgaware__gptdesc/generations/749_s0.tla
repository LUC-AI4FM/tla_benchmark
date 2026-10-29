---------------------------- MODULE MCCigaretteSmokers ----------------------------
(***************************************************************************)
(* Apalache-oriented type annotations and concrete helper definitions for *)
(* an instance of the CigaretteSmokers specification. The definitions of   *)
(* the CigaretteSmokers module are included here so that this module      *)
(* parses on its own. IngredientsVal and OffersVal are concrete model     *)
(* values intended for use from a configuration file.                     *)
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

-----------------------------------------------------------------------------
(* Concrete values for use from the configuration.                        *)

IngredientsVal == {"matches", "paper", "tobacco"}

OffersVal == {S \in SUBSET IngredientsVal : Cardinality(S) = 2}

-----------------------------------------------------------------------------
(* Contents of the CigaretteSmokers module.                               *)

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

vars == <<smokers, dealer>>

TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking ==
    /\ dealer /= {}
    /\ smokers' = [r \in Ingredients |->
                      [smoking |-> ({r} \cup dealer) = Ingredients]]
    /\ dealer' = {}

stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking = TRUE
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================
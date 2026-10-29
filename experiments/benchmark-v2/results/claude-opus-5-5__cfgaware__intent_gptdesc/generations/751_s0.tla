------------------------- MODULE CigaretteSmokers -------------------------
(***************************************************************************)
(* The cigarette smokers problem, generalised to an arbitrary finite set   *)
(* of ingredients.  Each smoker owns an infinite supply of exactly one     *)
(* ingredient, so smokers are identified with the ingredient they own.     *)
(* The dealer places an offer on the table: a set of ingredients that      *)
(* omits exactly one ingredient.  The smoker who owns the missing          *)
(* ingredient may take the offer and smoke.  When that smoker finishes,    *)
(* the dealer places a new offer.                                          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients,   \* the finite set of all ingredients (= smokers)
          Offers         \* the set of possible offers the dealer may make

ASSUME /\ IsFiniteSet(Ingredients)
       /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smokers,  \* smokers[r].smoking : whether smoker r is smoking
          dealer    \* current offer on the table ({} means the table is empty)

vars == <<smokers, dealer>>

(***************************************************************************)
(* Type and domain invariants                                              *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

\* Every non-empty offer omits exactly one ingredient.
ValidOffer == dealer /= {} =>
                 /\ dealer \subseteq Ingredients
                 /\ Cardinality(Ingredients \ dealer) = 1

\* Nobody smokes while an offer is still lying unused on the table.
SmokingWellFormed == (\E r \in Ingredients : smokers[r].smoking) => dealer = {}

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
Smoking == {r \in Ingredients : smokers[r].smoking}

\* Smoker r can use the current offer: it contains everything except r.
Enables(o, r) == /\ o /= {}
                 /\ r \notin o
                 /\ o \cup {r} = Ingredients

(***************************************************************************)
(* Initial state: nobody smokes and the dealer has placed some offer.      *)
(***************************************************************************)
Init == /\ smokers \in [Ingredients -> [smoking : {FALSE}]]
        /\ dealer \in Offers

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
\* Smoker r takes the offer from the table and starts smoking.
StartSmoking(r) ==
    /\ Enables(dealer, r)
    /\ Smoking = {}
    /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
    /\ dealer' = {}

\* Smoker r finishes smoking and signals completion.
StopSmoking(r) ==
    /\ smokers[r].smoking
    /\ dealer = {}
    /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ UNCHANGED dealer

\* The dealer places a new offer once the table is empty and nobody smokes.
Deal ==
    /\ dealer = {}
    /\ Smoking = {}
    /\ dealer' \in Offers
    /\ UNCHANGED smokers

Next == \/ \E r \in Ingredients : StartSmoking(r) \/ StopSmoking(r)
        \/ Deal

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Deal)
        /\ \A r \in Ingredients : WF_vars(StartSmoking(r))
        /\ \A r \in Ingredients : WF_vars(StopSmoking(r))

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
\* Safety: at most one smoker smokes at any time.
AtMostOne == Cardinality(Smoking) <= 1

\* Liveness: an offer that enables some smoker is eventually used.
OfferUsed == (\E r \in Ingredients : Enables(dealer, r))
                ~> (\E r \in Ingredients : smokers[r].smoking)

\* Progress: the dealer places offers infinitely often.
OffersProgress == []<>(dealer /= {})

=============================================================================
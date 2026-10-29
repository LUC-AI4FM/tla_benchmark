------------------------------ MODULE CigaretteSmokers ------------------------------
(***************************************************************************)
(* The classic cigarette smokers problem, generalised to any finite set   *)
(* of ingredients. Each smoker is identified with the one ingredient he    *)
(* has an infinite supply of. The dealer (environment) places an offer on  *)
(* the table. An offer is the full ingredient set minus exactly one        *)
(* ingredient. A smoker whose ingredient is the missing one may take the   *)
(* offer, smoke, and then signal completion. Only after that may the       *)
(* dealer place a new offer.                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients

ASSUME /\ IsFiniteSet(Ingredients)
       /\ Cardinality(Ingredients) >= 2   \* so that no offer is the empty set

VARIABLES
    dealer,    \* the set of ingredients currently on the table ({} = table empty)
    smokers    \* smokers[r].smoking : whether the smoker holding r is smoking

vars == <<dealer, smokers>>

(* Valid offers: every subset of Ingredients that omits exactly one ingredient *)
Offers == { Ingredients \ {i} : i \in Ingredients }

-----------------------------------------------------------------------------
(* Type and domain invariants *)

TypeOK ==
    /\ dealer \in Offers \cup {{}}
    /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]

ValidOffer ==
    dealer /= {} => /\ dealer \subseteq Ingredients
                    /\ Cardinality(Ingredients \ dealer) = 1

(* Smoking states are well formed: nobody smokes while an offer is still  *)
(* on the table (the smoker removed the ingredients when he started).     *)
WellFormedSmoking ==
    (\E r \in Ingredients : smokers[r].smoking) => dealer = {}

-----------------------------------------------------------------------------
Init ==
    /\ dealer \in Offers
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]

(* Smoker r takes the offer if it holds exactly the other ingredients. *)
StartSmoking(r) ==
    /\ dealer /= {}
    /\ dealer = Ingredients \ {r}
    /\ ~smokers[r].smoking
    /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
    /\ dealer' = {}

(* Smoker r finishes smoking and signals completion. *)
StopSmoking(r) ==
    /\ smokers[r].smoking
    /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ UNCHANGED dealer

(* The dealer places a new offer once the table is empty and nobody smokes. *)
Deal ==
    /\ dealer = {}
    /\ \A r \in Ingredients : ~smokers[r].smoking
    /\ dealer' \in Offers
    /\ UNCHANGED smokers

Next ==
    \/ Deal
    \/ \E r \in Ingredients : StartSmoking(r) \/ StopSmoking(r)

Fairness ==
    /\ WF_vars(Deal)
    /\ \A r \in Ingredients : WF_vars(StartSmoking(r))
    /\ \A r \in Ingredients : WF_vars(StopSmoking(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: at most one smoker smokes at any time. *)
AtMostOneSmokes ==
    \A r1, r2 \in Ingredients :
        (smokers[r1].smoking /\ smokers[r2].smoking) => r1 = r2

(* Liveness: an offer on the table is eventually used by some smoker. *)
OfferEventuallyTaken ==
    (dealer /= {}) ~> (\E r \in Ingredients : smokers[r].smoking)

(* Every offer enables some smoker, who eventually starts smoking. *)
EnabledSmokerEventuallySmokes ==
    \A r \in Ingredients :
        (dealer = Ingredients \ {r}) ~> (\E s \in Ingredients : smokers[s].smoking)

(* Progress: the dealer places offers again and again. *)
OffersRepeatedly ==
    []<>(dealer /= {})

THEOREM Spec => [](TypeOK /\ ValidOffer /\ WellFormedSmoking /\ AtMostOneSmokes)
THEOREM Spec => (OfferEventuallyTaken /\ EnabledSmokerEventuallySmokes /\ OffersRepeatedly)
=============================================================================
---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Naturals, FiniteSets

(*
  Parameterization:
  - INGREDIENTS: a finite nonempty set of ingredient identifiers (e.g., {matches, paper, tobacco})
  - OFFERS: a set of subsets of INGREDIENTS, each missing exactly one ingredient
  - None: a distinguished value not in INGREDIENTS or OFFERS, denoting absence (no offer / no smoker)
*)

CONSTANTS INGREDIENTS, OFFERS, None

ASSUME
  /\ IsFiniteSet(INGREDIENTS)
  /\ INGREDIENTS # {}
  /\ OFFERS \subseteq SUBSET INGREDIENTS
  /\ \A off \in OFFERS:
        /\ off \subseteq INGREDIENTS
        /\ Cardinality(off) = Cardinality(INGREDIENTS) - 1
  /\ None \notin INGREDIENTS
  /\ None \notin OFFERS

(*
  For each offer, exactly one ingredient is missing.
*)
UniqueMissing(off) == Cardinality(INGREDIENTS \ off) = 1

Missing(off) ==
  CHOOSE i \in INGREDIENTS : i \notin off

(*
  State variables:
  - table: current offer on the table, or None if the table is empty
  - smoking: the unique smoker (identified by their ingredient) currently smoking, or None
*)
VARIABLES table, smoking

vars == << table, smoking >>

Init ==
  /\ table = None
  /\ smoking = None

(*
  Dealer places an offer on the empty table when no one is smoking.
*)
DealerPlace(off) ==
  /\ table = None
  /\ smoking = None
  /\ off \in OFFERS
  /\ table' = off
  /\ UNCHANGED smoking

DealerPlace == \E off \in OFFERS : DealerPlace(off)

(*
  The smoker who holds the missing ingredient starts smoking by picking up the offered pair.
  This clears the table while they smoke.
*)
SmokerStart ==
  /\ table \in OFFERS
  /\ smoking = None
  /\ LET miss == Missing(table) IN
       /\ smoking' = miss
       /\ table' = None

(*
  The current smoker eventually finishes and signals the dealer to proceed.
*)
FinishSmoke ==
  /\ smoking \in INGREDIENTS
  /\ table = None
  /\ smoking' = None
  /\ UNCHANGED table

Next ==
  DealerPlace \/ SmokerStart \/ FinishSmoke

(*
  Safety invariants.
*)
TypeOK ==
  /\ (table = None) \/ (table \in OFFERS)
  /\ (smoking = None) \/ (smoking \in INGREDIENTS)

(*
  Mutual exclusion: at most one smoker may be smoking at any time.
  With our representation, the set of currently smoking smokers has cardinality <= 1.
*)
MutualExclusion ==
  Cardinality({ i \in INGREDIENTS : smoking = i }) <= 1

TableEmptyWhileSmoking ==
  (smoking \in INGREDIENTS) => (table = None)

OfferImpliesNoSmoking ==
  (table \in OFFERS) => (smoking = None)

SafetyInv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ TableEmptyWhileSmoking
  /\ OfferImpliesNoSmoking

(*
  Liveness properties.
  - Every offer eventually leads to some smoker smoking.
  - Every smoker that starts eventually finishes.
*)
OfferLeadsToSmoking ==
  [] ((table \in OFFERS) => <> (smoking \in INGREDIENTS))

SmokingEventuallyFinishes ==
  [] ((smoking \in INGREDIENTS) => <> (smoking = None))

(*
  Full behavior, with fairness ensuring progress:
  - Dealer fairly places offers when enabled.
  - Given an offer on the table, the corresponding smoker fairly starts.
  - A smoker fairly finishes when smoking.
*)
Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(DealerPlace)
  /\ WF_vars(SmokerStart)
  /\ WF_vars(FinishSmoke)

=============================================================================
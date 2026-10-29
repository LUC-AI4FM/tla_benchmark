---------------------------- MODULE CigaretteSmokers ----------------------------
(***************************************************************************)
(* The Cigarette Smokers Problem.                                          *)
(*                                                                         *)
(* Each smoker holds an infinite supply of exactly one ingredient, so      *)
(* smokers are identified with the ingredient they hold. A dealer          *)
(* repeatedly places an offer on the table. An offer is a set of           *)
(* ingredients containing all but one ingredient. The smoker holding the   *)
(* missing ingredient picks up the offer and smokes. When that smoker      *)
(* finishes, it signals the dealer, who then places a new offer.           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients,   \* e.g. {"matches", "paper", "tobacco"}
          Offers         \* subsets of Ingredients of size |Ingredients| - 1

ASSUME /\ Ingredients # {}
       /\ IsFiniteSet(Ingredients)
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smokers,   \* smokers[r].smoking : is the smoker holding r smoking?
          dealer,    \* the offer on the table ({} when the table is empty)
          done       \* TRUE when the dealer may place a new offer

vars == <<smokers, dealer, done>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
    /\ dealer \in Offers \cup {{}}
    /\ done \in BOOLEAN

Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer = {}
    /\ done = TRUE

(* The dealer selects an offer and places it on the table. *)
Deal ==
    /\ done
    /\ dealer = {}
    /\ \A r \in Ingredients : ~smokers[r].smoking
    /\ dealer' \in Offers
    /\ done' = FALSE
    /\ UNCHANGED smokers

(* The smoker holding the complementary ingredient picks up the offer
   and begins to smoke. *)
StartSmoking(r) ==
    /\ ~done
    /\ dealer # {}
    /\ r \notin dealer
    /\ dealer \cup {r} = Ingredients
    /\ \A s \in Ingredients : ~smokers[s].smoking
    /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
    /\ dealer' = {}
    /\ UNCHANGED done

(* The smoker finishes and signals the dealer to proceed. *)
StopSmoking(r) ==
    /\ smokers[r].smoking
    /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ done' = TRUE
    /\ UNCHANGED dealer

Next ==
    \/ Deal
    \/ \E r \in Ingredients : StartSmoking(r)
    \/ \E r \in Ingredients : StopSmoking(r)

Spec == Init /\ [][Next]_vars

Fairness ==
    /\ WF_vars(Deal)
    /\ \A r \in Ingredients : WF_vars(StartSmoking(r))
    /\ \A r \in Ingredients : WF_vars(StopSmoking(r))

FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety: at most one smoker smokes at any moment. *)
AtMostOneSmoker ==
    Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

(* The table is empty while someone is smoking. *)
TableEmptyWhileSmoking ==
    (\E r \in Ingredients : smokers[r].smoking) => dealer = {}

(* Liveness: every offer placed on the table eventually leads to a smoker
   smoking. *)
OfferLeadsToSmoking ==
    \A o \in Offers :
        (dealer = o) ~> (\E r \in Ingredients : smokers[r].smoking)

(* Liveness: whoever smokes eventually finishes. *)
SmokerFinishes ==
    \A r \in Ingredients : smokers[r].smoking ~> ~smokers[r].smoking

(* Liveness: the system never stalls; someone smokes infinitely often. *)
InfinitelyOftenSmoking ==
    []<>(\E r \in Ingredients : smokers[r].smoking)

THEOREM Spec => [](TypeOK /\ AtMostOneSmoker /\ TableEmptyWhileSmoking)
THEOREM FairSpec => OfferLeadsToSmoking /\ SmokerFinishes /\ InfinitelyOftenSmoking
=============================================================================
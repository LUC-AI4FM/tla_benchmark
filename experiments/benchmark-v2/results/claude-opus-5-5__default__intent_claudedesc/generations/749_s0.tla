-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* The Cigarette Smokers Problem.                                          *)
(*                                                                         *)
(* A dealer repeatedly places on the table all but one of the ingredients  *)
(* needed to make a cigarette. Each smoker holds an infinite supply of     *)
(* exactly one ingredient. The smoker holding the missing ingredient picks *)
(* up the offered ones and smokes. When that smoker finishes, the dealer   *)
(* offers a new combination.                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients,   \* the set of ingredients, one smoker per ingredient
          Offers         \* the combinations the dealer may place on the table

ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smokers,       \* smokers[r].smoking : is the smoker holding r smoking?
          dealer         \* the ingredients on the table ({} if none)

vars == <<smokers, dealer>>

(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

(***************************************************************************)
(* Initial state: nobody smokes; the dealer has placed a valid offer.      *)
(***************************************************************************)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* The smoker whose ingredient complements the offer picks up the          *)
(* ingredients from the table and starts smoking.                          *)
(***************************************************************************)
StartSmoking(r) ==
    /\ dealer /= {}
    /\ r \notin dealer
    /\ dealer \cup {r} = Ingredients
    /\ \A s \in Ingredients : ~smokers[s].smoking
    /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
    /\ dealer' = {}

(***************************************************************************)
(* The smoking smoker finishes, and the dealer then offers a new           *)
(* combination o.                                                          *)
(***************************************************************************)
StopSmoking(r, o) ==
    /\ dealer = {}
    /\ smokers[r].smoking
    /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' = o

Next == \/ \E r \in Ingredients : StartSmoking(r)
        \/ \E r \in Ingredients, o \in Offers : StopSmoking(r, o)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Fairness: smokers eventually pick up a matching offer; the dealer       *)
(* eventually offers each combination that is repeatedly possible.         *)
(***************************************************************************)
FairSpec ==
    /\ Spec
    /\ \A r \in Ingredients : WF_vars(StartSmoking(r))
    /\ \A o \in Offers : SF_vars(\E r \in Ingredients : StopSmoking(r, o))
    /\ WF_vars(\E r \in Ingredients, o \in Offers : StopSmoking(r, o))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

\* The table is empty exactly when somebody is smoking.
TableConsistent ==
    (dealer = {}) <=> (\E r \in Ingredients : smokers[r].smoking)

Inv == TypeOK /\ AtMostOne

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* The system keeps operating: someone smokes infinitely often.
Progress == []<>(\E r \in Ingredients : smokers[r].smoking)

\* Whenever an offer is on the table, the matching smoker eventually smokes.
OfferLeadsToSmoking ==
    \A r \in Ingredients :
        (dealer = Ingredients \ {r}) ~> smokers[r].smoking

\* Every smoker whose complement can be offered smokes infinitely often.
EverySmokerSmokes ==
    \A r \in Ingredients :
        ((Ingredients \ {r}) \in Offers) => []<>(smokers[r].smoking)

THEOREM Spec => [](TypeOK /\ AtMostOne /\ TableConsistent)
THEOREM FairSpec => Progress /\ OfferLeadsToSmoking /\ EverySmokerSmokes
=============================================================================
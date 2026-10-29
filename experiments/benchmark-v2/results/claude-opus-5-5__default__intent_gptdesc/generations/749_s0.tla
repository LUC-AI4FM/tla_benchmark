------------------------------ MODULE CigaretteSmokers ------------------------------
EXTENDS FiniteSets

CONSTANTS Paper, Tobacco, Matches

ASSUME Paper # Tobacco /\ Tobacco # Matches /\ Paper # Matches

Ingredients == {Paper, Tobacco, Matches}

(* Each smoker is identified by the single ingredient it holds infinitely. *)
Smokers == Ingredients

(* Possible deals: pairs of distinct ingredients. *)
Pairs == { p \in SUBSET Ingredients : Cardinality(p) = 2 }

Complement(s) == Ingredients \ {s}

VARIABLES
    table,      \* set of ingredients currently on the table
    dealer,     \* "ready" (may deal) or "waiting" (waiting for completion signal)
    smoker,     \* smoker[s] \in {"idle", "taking", "smoking"}
    holding,    \* holding[s] = ingredients smoker s has taken from the table
    lastDeal    \* the pair most recently placed by the dealer ({} initially)

vars == <<table, dealer, smoker, holding, lastDeal>>

SmokerStates == {"idle", "taking", "smoking"}

TypeOK ==
    /\ table \subseteq Ingredients
    /\ dealer \in {"ready", "waiting"}
    /\ smoker \in [Smokers -> SmokerStates]
    /\ holding \in [Smokers -> SUBSET Ingredients]
    /\ lastDeal \in Pairs \cup {{}}

AllIdle == \A s \in Smokers : smoker[s] = "idle"

-----------------------------------------------------------------------------
Init ==
    /\ table = {}
    /\ dealer = "ready"
    /\ smoker = [s \in Smokers |-> "idle"]
    /\ holding = [s \in Smokers |-> {}]
    /\ lastDeal = {}

(* Dealer places a pair of distinct ingredients on an empty table, only when *)
(* no smoker is taking ingredients or smoking.                               *)
Deal(pair) ==
    /\ dealer = "ready"
    /\ table = {}
    /\ AllIdle
    /\ table' = pair
    /\ lastDeal' = pair
    /\ dealer' = "waiting"
    /\ UNCHANGED <<smoker, holding>>

DealerStep == \E pair \in Pairs : Deal(pair)

(* The smoker holding the complementary ingredient detects the pair and     *)
(* takes both items atomically; only one smoker can take per deal.          *)
Take(s) ==
    /\ smoker[s] = "idle"
    /\ table # {}
    /\ table = Complement(s)
    /\ \A t \in Smokers \ {s} : smoker[t] = "idle"
    /\ holding' = [holding EXCEPT ![s] = table]
    /\ table' = {}
    /\ smoker' = [smoker EXCEPT ![s] = "taking"]
    /\ UNCHANGED <<dealer, lastDeal>>

(* Smoker makes and lights the cigarette. *)
Smoke(s) ==
    /\ smoker[s] = "taking"
    /\ smoker' = [smoker EXCEPT ![s] = "smoking"]
    /\ UNCHANGED <<table, dealer, holding, lastDeal>>

(* Smoker finishes, consumes the ingredients and signals the dealer. *)
Finish(s) ==
    /\ smoker[s] = "smoking"
    /\ smoker' = [smoker EXCEPT ![s] = "idle"]
    /\ holding' = [holding EXCEPT ![s] = {}]
    /\ dealer' = "ready"
    /\ UNCHANGED <<table, lastDeal>>

SmokerStep(s) == Take(s) \/ Smoke(s) \/ Finish(s)

Next ==
    \/ DealerStep
    \/ \E s \in Smokers : SmokerStep(s)

Fairness ==
    /\ WF_vars(DealerStep)
    /\ \A s \in Smokers : WF_vars(Take(s))
    /\ \A s \in Smokers : WF_vars(Smoke(s))
    /\ \A s \in Smokers : WF_vars(Finish(s))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* At most one smoker is smoking at any time. *)
AtMostOneSmoking ==
    \A s1, s2 \in Smokers :
        (smoker[s1] = "smoking" /\ smoker[s2] = "smoking") => s1 = s2

(* A smoker only takes/smokes after the dealer placed exactly its complement. *)
SmokeOnlyComplement ==
    \A s \in Smokers :
        smoker[s] \in {"taking", "smoking"} =>
            /\ lastDeal = Complement(s)
            /\ holding[s] = lastDeal

(* No loss or duplication: while a deal is outstanding, its ingredients are *)
(* either all on the table or all held by exactly one smoker, never both.   *)
NoLossOrDuplication ==
    /\ dealer = "waiting" =>
         \/ /\ table = lastDeal
            /\ \A s \in Smokers : holding[s] = {}
         \/ /\ table = {}
            /\ \E s \in Smokers :
                  /\ holding[s] = lastDeal
                  /\ \A t \in Smokers \ {s} : holding[t] = {}
    /\ dealer = "ready" =>
         /\ table = {}
         /\ AllIdle
         /\ \A s \in Smokers : holding[s] = {}

(* Table contents: empty, or exactly the last dealt pair of two ingredients. *)
TableInvariant ==
    \/ table = {}
    \/ /\ table \in Pairs
       /\ table = lastDeal
       /\ dealer = "waiting"

(* Exclusive access: at most one smoker is active, and while one is active *)
(* the table is empty and the dealer cannot deal.                          *)
ExclusiveAccess ==
    /\ \A s1, s2 \in Smokers :
          (smoker[s1] # "idle" /\ smoker[s2] # "idle") => s1 = s2
    /\ \A s \in Smokers :
          smoker[s] # "idle" => (table = {} /\ dealer = "waiting")

(* A smoker never holds its own ingredient from the table. *)
NeverTakesOwn ==
    \A s \in Smokers : s \notin holding[s]

Safety ==
    /\ TypeOK
    /\ AtMostOneSmoking
    /\ SmokeOnlyComplement
    /\ NoLossOrDuplication
    /\ TableInvariant
    /\ ExclusiveAccess
    /\ NeverTakesOwn

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Every deal is eventually consumed by the correct smoker. *)
DealConsumedByCorrectSmoker ==
    \A s \in Smokers :
        (table = Complement(s)) ~> (smoker[s] = "smoking")

(* Every deal eventually completes, enabling the dealer again. *)
DealCompletes ==
    (dealer = "waiting") ~> (dealer = "ready")

(* The dealer is always eventually able to place another pair. *)
DealerProgress ==
    []<>(dealer = "ready") /\ []<>(table # {})

(* Each smoker that starts taking eventually finishes. *)
SmokerFinishes ==
    \A s \in Smokers :
        (smoker[s] = "taking") ~> (smoker[s] = "idle")

Liveness ==
    /\ DealConsumedByCorrectSmoker
    /\ DealCompletes
    /\ DealerProgress
    /\ SmokerFinishes

THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================
MODULE SmokersProblem
EXTENDS TLC

CONSTANTS INGREDIENTS, Smoker, Missing

VARIABLE dealerOffer, smokerFlags

Init ==
    /\ dealerOffer \in SUBSET INGREDIENTS
    /\ (# dealerOffer = (# INGREDIENTS) - 1)
    /\ smokerFlags \in [Smoker -> BOOLEAN]
    /\ \A s \in Smoker : smokerFlags[s] = FALSE

DealerAction ==
    /\ \A f \in Smoker : smokerFlags[f] = FALSE
    /\ dealerOffer' \in SUBSET INGREDIENTS
    /\ (# dealerOffer' = (# INGREDIENTS) - 1)
    /\ \E m \in INGREDIENTS :
        dealerOffer' = INGREDIENTS \ {m}
    /\ smokerFlags' = smokerFlags

StartSmoking ==
    /\ \A f \in Smoker : smokerFlags[f] = FALSE
    /\ \E s \in Smoker :
        /\ Missing[s] \notin dealerOffer
        /\ smokerFlags' = [smokerFlags EXCEPT ![s] = TRUE]
    /\ UNCHANGED dealerOffer

StopSmoking ==
    /\ \E s \in Smoker : smokerFlags[s] = TRUE
    /\ smokerFlags' = [f \in Smoker |-> FALSE]
    /\ UNCHANGED dealerOffer

Next == DealerAction \/ StartSmoking \/ StopSmoking

AtMostOne == # {s \in Smoker : smokerFlags[s]} <= 1

Spec == Init /\ [][Next]_(dealerOffer, smokerFlags) /\ WF_vars(Next)

===============================================================================
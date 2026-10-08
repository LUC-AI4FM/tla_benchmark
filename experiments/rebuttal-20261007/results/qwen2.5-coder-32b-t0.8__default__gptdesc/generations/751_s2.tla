---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    INGREDIENTS  \* A set of ingredients, e.g., {"paper", "matches", "tobacco"}

VARIABLES
    dealerOffer,  \* The current offer by the dealer (a subset of INGREDIENTS with one ingredient missing)
    smokerSmoking \* Flags indicating which smoker is currently smoking

Init == /\ dealerOffer \in SUBSET INGREDIENTS 
        /\ Cardinality(dealerOffer) = Cardinality(INGREDIENTS) - 1
        /\ smokerSmoking \in [ {"paper", "matches", "tobacco"} -> BOOLEAN ]
        /\ \A s \in {"paper", "matches", "tobacco"}: smokerSmoking[s] = FALSE

Next == \/ \E s \in INGREDIENTS \ dealerOffer : 
              /\ smokerSmoking' = [smokerSmoking EXCEPT ![s] = TRUE]
              /\ dealerOffer' \notin SUBSET INGREDIENTS
          \/ \A s \in {"paper", "matches", "tobacco"}: smokerSmoking[s] => 
              /\ smokerSmoking' = [smokerSmoking EXCEPT ![s] = FALSE]
              /\ dealerOffer' \in SUBSET INGREDIENTS
              /\ Cardinality(dealerOffer') = Cardinality(INGREDIENTS) - 1

AtMostOne == \/ \A s1, s2 \in {"paper", "matches", "tobacco"}: 
                   s1 # s2 => ~(smokerSmoking[s1] /\ smokerSmoking[s2])

Spec == Init /\ [][Next]_<<dealerOffer, smokerSmoking>>

FairSpec == Spec /\ WF_next(<<dealerOffer, smokerSmoking>>)

=============================================================================
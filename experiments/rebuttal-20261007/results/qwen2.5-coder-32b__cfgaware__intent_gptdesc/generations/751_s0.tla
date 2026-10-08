------------------------------- MODULE CigaretteSmokers -------------------------------

CONSTANTS Ingredients  \* The set of all ingredients

VARIABLES offer, smoking  \* offer is a subset of Ingredients missing exactly one ingredient, smoking is the smoker currently smoking (or FALSE if no one is smoking)

ASSUME Cardinality(Ingredients) >= 2  \* There must be at least two ingredients for the problem to make sense

TypeOK == 
    /\ offer \in SUBSET Ingredients
    /\ Cardinality(offer) = Cardinality(Ingredients) - 1
    /\ (smoking \in (Ingredients \cup {FALSE}))

AtMostOne ==
    \/ smoking = FALSE
    \/ (\A i, j \in Ingredients : i # j => (i /= smoking) \/ (j /= smoking))

SmokersEnabled ==
    [s \in Ingredients |-> offer = (Ingredients \ {s})]

Next ==
    \/ /\ smoking = FALSE
       /\ \E s \in Ingredients : SmokersEnabled[s]
       /\ offer' = offer
       /\ smoking' = CHOOSE s \in Ingredients : SmokersEnabled[s]
    \/ /\ smoking # FALSE
       /\ offer' \in SUBSET Ingredients
       /\ Cardinality(offer') = Cardinality(Ingredients) - 1
       /\ smoking' = FALSE

Spec ==
    /\ TypeOK
    /\ AtMostOne
    /\ [][\E s \in Ingredients : SmokersEnabled[s] => <>[]smoking = s]
    /\ []<>TypeOK
    /\ \/ smoking # FALSE
       \/ <>(\E offer'' \in SUBSET Ingredients : Cardinality(offer'') = Cardinality(Ingredients) - 1 /\ [][Next]_<<offer, smoking>>)

=============================================================================
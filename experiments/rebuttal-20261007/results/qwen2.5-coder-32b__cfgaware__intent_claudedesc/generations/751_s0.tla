------------------------------- MODULE CigaretteSmokersProblem -------------------------------

CONSTANTS Ingredients, Offers

ASSUME Cardinality(Ingredients) = 3
ASSUME \A offer \in Offers : Cardinality(offer) = Cardinality(Ingredients) - 1

VARIABLES table, smoking

TypeOK == /\ table \in Offers
          /\ smoking \in (Ingredients \cup {FALSE})

AtMostOne == smoking \in {FALSE} \cup Ingredients

Init == \/ table = << >> 
        /\ smoking = FALSE

Next ==
    \/ /\ smoking = FALSE
       /\ \E offer \in Offers : table = offer
       /\ \E smoker \in Ingredients \ table : smoking = smoker
    \/ /\ smoking \in Ingredients
       /\ table = {smoking}
       /\ smoking' = FALSE
       /\ \E offer \in Offers : table' = offer

Spec ==
    /\ Init
    /\ [][Next]_<<table, smoking>>
    /\ WF_next(<<table, smoking>>)

WF_next(vars) == 
    \/ vars = << >> 
    \/ \A s \in (Ingredients \cup {FALSE}) :
        \E t \in Offers : 
            <</\X: Ingredients \ {s} : X, s>>_vars => <</t, FALSE>>_vars

=============================================================================
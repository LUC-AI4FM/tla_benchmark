------------------------------- MODULE CigaretteSmokersProblem -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS INGREDIENTS, OFFERS

VARIABLES table, smoking

Init == /\ table \in OFFERS
        /\ smoking = FALSE

Next ==
    \/ /\ \E offer \in OFFERS : table = offer
       /\ \E ingredient \in INGREDIENTS \ offer :
            \/ /\ smoking = FALSE
               /\ smoking' = TRUE
               /\ table' = {}
    \/ /\ smoking = TRUE
       /\ smoking' = FALSE
       /\ \E offer \in OFFERS : table' = offer

Spec ==
    /\ Init
    /\ [][Next]_<<table, smoking>>
    /\ WF_next(<<table, smoking>>)

MutualExclusion == [](smoking => []<>(~smoking))

Fairness ==
    \/ \A offer \in OFFERS :
        WF[table = offer]
        -> <>[\E ingredient \in INGREDIENTS \ offer : smoking]

=============================================================================
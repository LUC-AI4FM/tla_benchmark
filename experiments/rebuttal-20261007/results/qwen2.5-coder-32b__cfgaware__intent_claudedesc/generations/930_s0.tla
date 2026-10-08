------------------------------- MODULE Clock -------------------------------

CONSTANTS HC, HCini

VARIABLE hour

HC == 1 \leq hour \leq 12

HCini == /\ HC
         /\ hour = HCini

Next ==
    \/ /\ HC
       /\ hour' = IF hour < 12 THEN hour + 1 ELSE 1
    \/ /\ HC
       /\ hour' = hour

Spec ==
    /\ HCini
    /\ [][Next]_<<hour>>

THEOREM Spec => []HC

=============================================================================
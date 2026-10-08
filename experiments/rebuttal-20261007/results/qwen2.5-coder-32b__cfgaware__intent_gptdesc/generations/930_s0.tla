------------------------------- MODULE Clock -------------------------------

CONSTANTS HC, HCini

VARIABLE hour

HC == 1..12

HCini == hour \in HC

Init == HCini

Next ==
    /\ hour' = IF hour < 12 THEN hour + 1 ELSE 1
    /\ hour' \in HC

Spec ==
    /\ Init
    /\ [][Next]_<<hour>>

Inv ==
    /\ hour \in HC
    /\ (hour' = IF hour < 12 THEN hour + 1 ELSE 1)

Fairness == 
    WF_next(<<hour>>)

THEOREM Spec => []Inv

THEOREM Spec => <>[]HC

=============================================================================
MODULE Clock12
VARIABLES hr

HCini == hr >= 1 /\ hr <= 12

HCnxt ==
   /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1
   /\ TRUE

Next == HCnxt

Init == HCini

Spec == Init /\ [][Next]_vars

THEOREM InvariantMaintained : [] HCini
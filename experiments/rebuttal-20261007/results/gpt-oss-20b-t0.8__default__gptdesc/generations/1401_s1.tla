MODULE Counter
   EXTENDS Naturals, TLC

VARIABLES outerX

Init == outerX = 0

Step ==
   IF outerX < 3 THEN outerX' = outerX + 1 ELSE FALSE

Next ==
   IF outerX < 3 THEN
      outerX' = outerX + 1
   ELSE
      outerX' = outerX

WF == WF_vars(outerX)(Step)

Liveness == <> (outerX = 3)

Spec == Init /\ [][Next]_outerX /\ WF /\ Liveness
====
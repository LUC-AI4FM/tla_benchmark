---- MODULE SimpleClock ----

VARIABLE hr

HCini == 1 <= hr /\ hr <= 12

HCnxt == \/ hr' = (hr % 12) + 1
         \/ hr' = hr

HC == HCini /\ [](HCnxt \/ []<<hr' = hr>>)

THEOREM HC => []HCini

====
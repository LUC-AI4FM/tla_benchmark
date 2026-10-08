---------------------------- MODULE Clock ---------------------------------
HC == 1..12
HCini == (HC \in 1..12)

VARIABLES HC

Clock == [*][*]HC' = IF HC = 12 THEN 1 ELSE HC + 1

THEOREM THEOREM_Clock_Validity == 
  Spec => []HC \in 1..12
Spec == (HCini) /\
       [][*]Clock
=============================================================================
---- MODULE HourClock ----
EXTENDS Integers, TLC

VARIABLE h

Hours == 1..12
Vars  == << h >>

Init == h \in Hours

NextInc == h' = IF h # 12 THEN h + 1 ELSE 1

NextMod == h' = (h mod 12) + 1

TypeInv == h \in Hours

Safety == []TypeInv

PointwiseEq == \A x \in Hours :
  (IF x # 12 THEN x + 1 ELSE 1) = ((x mod 12) + 1)

AlwaysEnabledInc == [](TypeInv => Enabled NextInc)
AlwaysEnabledMod == [](TypeInv => Enabled NextMod)

EquivAction == [](TypeInv => (NextInc <=> NextMod))

Recurrence == \A k \in Hours : []<>(h = k)

HC  == Init /\ [][NextInc]_Vars /\ WF_Vars(NextInc)

HC2 == Init /\ [][NextMod]_Vars /\ WF_Vars(NextMod)
====
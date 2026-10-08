MODULE ClockEquivalence
EXTENDS HourClock

CONSTANT initHour

VARIABLES hour

vars == <<hour>>

Init ==
  hour = initHour /\ initHour \in 1..12

NextPrimary ==
  \/ (hour = 12 /\ hour' = 1)
  \/ (hour # 12 /\ hour' = hour + 1)

NextModular ==
  hour' = ((hour - 1) % 12) + 1

SpecPrimary == Init /\ [][NextPrimary]_vars
SpecModular == Init /\ [][NextModular]_vars

Theorem NextRelationEquivalence ==
  \A h, hp : ((h = 12 /\ hp = 1) \/ (h # 12 /\ hp = h + 1)) <=> (hp = ((h - 1) % 12) + 1)

Theorem PrimaryImpliesModular == SpecPrimary => SpecModular
Theorem ModularImpliesPrimary == SpecModular => SpecPrimary

===============================================================================
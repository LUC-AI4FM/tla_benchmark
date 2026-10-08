------------------------------ MODULE Clock12 ------------------------------

EXTENDS Integers

CONSTANTS Low, High

ASSUME Low = 1 /\ High = 12 /\ Low < High

VARIABLES hour

H == Low..High

Succ(h) ==
  IF h = High THEN Low ELSE h + 1

Init ==
  hour \in H

Next ==
  hour' = Succ(hour)

Spec ==
  Init /\ [] Next /\ SF_hour(Next)

\* Safety: hour stays within 1..12
TypeInvariant ==
  hour \in H

SafetyInvariant ==
  [] TypeInvariant

\* Functional correctness: every step advances by 1 modulo 12
FunctionalCorrectness ==
  [] (hour' = Succ(hour))

\* Preservation: each transition keeps hour in 1..12
Preservation ==
  TypeInvariant /\ Next => TypeInvariant'

\* Liveness/recurrence: under fair execution, every hour appears infinitely often
LivenessCycle ==
  \A h \in H : []<>(hour = h)

=============================================================================
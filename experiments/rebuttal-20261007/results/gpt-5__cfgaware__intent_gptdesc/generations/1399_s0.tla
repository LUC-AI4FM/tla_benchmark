---- MODULE Toggle ----

EXTENDS Sequences

VARIABLES s

Init ==
  s = TRUE

Flip ==
  /\ s \in BOOLEAN
  /\ s' = ~s

Next ==
  Flip

TypeInv ==
  s \in BOOLEAN

Safety ==
  []TypeInv

StrongAlwaysTrue ==
  [](s = TRUE)

WeakObservational ==
  [](s \in BOOLEAN)

AlwaysEnabled ==
  []ENABLED Next

NoDeadlock ==
  []ENABLED [Next]_s

Spec ==
  Init /\ [][Next]_s

Prop ==
  Safety /\ AlwaysEnabled

====
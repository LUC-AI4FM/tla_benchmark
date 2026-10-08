```
MODULE PrisonersAndSwitches

CONSTANT Prisoner
VARIABLE p2, p3

p1 == CHOOSE p \in Prisoner : p /= "counter"

Spec ==
  /\ p2 \in [Prisoner -> {0, 1}]
  /\ p3 \in [Prisoner -> {0, 1}]
  /\ (p2["counter"] = 0) /\ (p3["counter"] = 0)
  /\ [][
      /\ \E p \in Prisoner :
        /\ IF p /= "counter"
          THEN
            /\ (p2' = [p2 EXCEPT ![p] = IF p2[p] = 0 THEN 1 ELSE 0])
            /\ (p3' = p3)
          ELSE
            /\ (p2' \in [Prisoner -> {0, 1}])
            /\ (p3' \in [Prisoner -> {0, 1)])
      /\ UNCHANGED << >>
    ]

TypeOK ==
  /\ p2 \in [Prisoner -> {0, 1}]
  /\ p3 \in [Prisoner -> {0, 1}]

CountInvariant ==
  /\ TypeOK
  /\ (p2["counter"] = Cardinality({p \in Prisoner : p2[p] = 1}))

Safety ==
  Spec
  ==> [](TypeOK => (p2["counter"] = Cardinality(Prisoner)) => \A p \in Prisoner : p2[p] = 1)

Liveness ==
  Spec
  ==> <>[]<>(\A p \in Prisoner : p2[p] = 1)
```
Note: The `UNCHANGED` operator is used to specify that all other variables remain unchanged in a step. The `Cardinality` function returns the number of elements in a set. The `EXCEPT` operator is used to create a new function by modifying an existing one at a specific point.
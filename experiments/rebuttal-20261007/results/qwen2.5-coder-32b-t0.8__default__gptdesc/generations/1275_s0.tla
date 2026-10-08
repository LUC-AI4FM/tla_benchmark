```tla
MODULE InitializationPattern

EXTENDS Integers, TLC

CONSTANTS Init

VARIABLES s

Init == \E v \in 0..1 : s = v /\ s < 1

Next == UNCHANGED s

Spec ==
  \/ /\ Init
     /\ []Next_s
  \/ /\ Init
     /\ []Inv_s

Inv == s < 1

```

```tla
\* Fairness conditions not mentioned in the description, so omitted.
```
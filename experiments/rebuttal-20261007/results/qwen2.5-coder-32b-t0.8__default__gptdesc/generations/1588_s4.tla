```tla
MODULE EuclidsAlgorithm

EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES u, v, v_ini, pc

Init == /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "Start"

Next ==
    CASE pc = "Start" ->
         /\ u > v
         /\ pc' = "Subtract"
    [] pc = "Subtract" ->
         /\ IF u > v THEN u' = u - v ELSE u' = u
         /\ IF u > v THEN v' = v ELSE v' = u - v
         /\ pc' = "Check"
    [] pc = "Check" ->
         /\ IF v = 0 THEN pc' = "Done" ELSE pc' = "Subtract"

Spec ==
    /\ Init
    /\ [][Next]_<<u, v, v_ini, pc>>
    /\ WF_next(Next)

Termination == <>[](pc = "Done")

====

```

```tla
\* Modification to include fairness and liveness properties
Liveness ==
    <>[](pc = "Done")

SpecWithFairness ==
    Spec
    /\ Liveness

WF_next(f) == <>([]f)
```
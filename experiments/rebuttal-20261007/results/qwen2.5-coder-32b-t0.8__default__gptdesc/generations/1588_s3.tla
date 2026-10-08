```tla
MODULE EuclidsAlgorithm

EXTENDS Integers, TLC

CONSTANTS N

VARIABLES u, v, v_ini, pc

Init == /\ u = 24 
        /\ v \in 1..N 
        /\ v_ini = v 
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
             /\ u >= v
             /\ u' = u - v
             /\ v' = v
             /\ v_ini' = v_ini
             /\ pc' = "Subtract"
          \/ /\ pc = "Start"
             /\ u < v
             /\ u' = u
             /\ v' = v
             /\ v_ini' = v_ini
             /\ pc' = "Swap"
          \/ /\ pc = "Subtract"
             /\ u >= v
             /\ u' = u - v
             /\ v' = v
             /\ v_ini' = v_ini
             /\ pc' = "Subtract"
          \/ /\ pc = "Subtract"
             /\ u < v
             /\ u' = u
             /\ v' = v
             /\ v_ini' = v_ini
             /\ pc' = "Swap"
          \/ /\ pc = "Swap"
             /\ u' = v
             /\ v' = u
             /\ v_ini' = v_ini
             /\ pc' = "Subtract"

Spec == Init /\ [][Next]_<<u, v, v_ini, pc>> /\ WF_next(Next)

WF_next(next) == <<u, v, v_ini, pc>> \in (Init => UNCHANGED <<u, v, v_ini>>) \/ next)

Termination == <>[](pc = "Done")

(* Fairness *)
Fairness == WF[<<u, v, v_ini, pc>>, Next]

SpecWithFairness == Spec /\ Fairness

INV_1 == u >= 0 /\ v > 0
INV_2 == v <= v_ini

THEOREMS INV_1 \* GCD invariant
THEOREMS INV_2 \* Initial value of v is never exceeded
THEOREMS Termination \* The algorithm terminates
```
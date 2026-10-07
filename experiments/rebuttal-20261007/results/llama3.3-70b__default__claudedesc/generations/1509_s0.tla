```
MODULE ModuleI
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == x \in {1, 2, 3, 4, 5}

N[i \in {1, 2, 3}] == UNCHANGED <<x>>

Next == \E i \in {1, 2, 3} : N[i]

F[1] == 1
F[i \in {2, 3, 4, 5}] == F[i-1] + 1

Inv == \E i \in {1, 2, 3, 4, 5} : F[i] = x

Spec == Init /\ [][Next]_x
```
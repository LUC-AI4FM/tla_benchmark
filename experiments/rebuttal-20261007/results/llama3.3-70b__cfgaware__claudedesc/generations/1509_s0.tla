```
MODULE ModuleI
VARIABLE x

F[i \in {1,2,3,4,5}] == IF i = 1 THEN 1 ELSE F[i-1] + 1

Inv == \E i \in {1,2,3,4,5} : F[i] = x

N[i \in {1,2,3}] == UNCHANGED <<x>>

Init == x \in {1,2,3,4,5}

Next == \E i \in {1,2,3} : N[i]

Spec == Init /\ [][Next]_<<x>>
```
Note: The `UNCHANGED` operator is used to specify that the variable `x` does not change in the next-state relation. The recursive function `F` is defined using the `==` operator for equality and the `IF` statement for conditional expression. The invariant `Inv` asserts the existence of an index `i` such that `F[i] = x`. The action `N[i]` leaves `x` unchanged, and the next-state relation `Next` allows any of these actions to occur. Finally, the specification `Spec` is defined as the conjunction of the initial condition `Init` and the infinite conjunction of the next-state relation `[Next]_<<x>>`.
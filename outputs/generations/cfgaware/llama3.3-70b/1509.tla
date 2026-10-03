```
MODULE SmallSystem
VARIABLE x

Const == {1, 2, 3, 4, 5}
Indices == {1, 2, 3}

F[1] == 1
F[n \in (Const \ {1})] == F[n-1] + 1

N[i \in Indices](x) == x' = F[x]

Spec == x = 1 /\ [][\E i \in Indices : N[i](x)]_x

Inv == x \in {F[n] : n \in Const}

THEOREM Spec => []Inv
```
Note: This TLA+ module defines the required constants, variables, and operators. The `F` operator is defined recursively over the set `Const`, and the `N` operator is defined for each index in `Indices`. The `Spec` temporal formula requires that `x` initially equals 1 and that all steps satisfy an existentially quantified indexed action under stuttering. The `Inv` invariant relates `x` to values of `F`.
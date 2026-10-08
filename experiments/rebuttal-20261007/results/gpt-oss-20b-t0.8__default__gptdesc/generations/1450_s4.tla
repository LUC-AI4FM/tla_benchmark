```
MODULE RandomSubsetSample
CONSTANTS S, T

VARIABLE x

(* Type assumption: x is a total function from S to T *)
TypeOK == x \in [S -> T]

Init  == TypeOK

Next  == x' = x

Inv   == TRUE

Spec  == Init /\ [][Next]_x
```
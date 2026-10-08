```
MODULE WeighingPiece
EXTENDS Integers, FiniteSets

CONSTANTS W, N

VARIABLES pieces

Init == (pieces \in [1..W -> Nat] /\ (* pieces is a function from 1 to N to positive integers *)
        Cardinality(Domain(pieces)) = N)

Next == (pieces' \in [1..W -> Nat] /\ 
         Cardinality(Domain(pieces')) = N /\ 
         (\A i \in Domain(pieces): pieces'[i] > 0) /\ 
         (* sum of weights of new pieces equals W *)
         Sum({<<i, pieces'[i]> | i \in Domain(pieces')}) = W)

Spec == Init /\ [][Next]_pieces

THEOREM Spec => [](Cardinality(Domain(pieces)) = N)
THEOREM Spec => [](\A t \in 1..W: 
                  \E (coeffs \in [1..N -> {-1,0,1}]):
                    Sum({<<i, coeffs[i]*pieces[i]> | i \in Domain(pieces)}) = t)

THEOREM Spec => [](Sum({<<i, pieces[i]> | i \in Domain(pieces)}) = W)
THEOREM Spec => [](\A i \in Domain(pieces): pieces[i] > 0)
```
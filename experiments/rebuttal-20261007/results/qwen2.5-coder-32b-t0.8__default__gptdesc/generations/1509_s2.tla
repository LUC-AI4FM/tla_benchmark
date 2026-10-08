```tla
MODULE SmallSystem

EXTENDS Naturals, TLC

CONSTANTS Domain

VARIABLES x

F == [n \in {1,2,3,4,5} |-> IF n = 1 THEN 2 ELSE F[n-1] + 2]

N[i] == CASE i = 1 -> x' = F[1]
          []   i = 2 -> x' = F[x]
          []   i = 3 -> x' = F[F[x]]

Init == x \in {1,2,3,4,5}

Next == \/ (\E i \in {1,2,3} : N[i])
        \/ x' = x

Spec == Init /\ [][Next]_<<x>>

Inv == x \in {1,2,3,4,5} /\ x = F[x]

ENDMODULE
```
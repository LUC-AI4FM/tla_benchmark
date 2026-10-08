```
MODULE DijkstraTokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, K
ASSUME K > N && N > 0

VARIABLES values

Init == (values \in [1..N -> 0..(K-1)])

Next == 
  /\ IF values[1] = values[N]
     THEN values' = [values EXCEPT !1 = (values[1] + 1) % K]
     ELSE values' = values
  /\ FORALL i \in (2..N) : 
       IF values[i] # values[(i-1)]
          THEN values' = [values EXCEPT !i = values[(i-1)]]
          ELSE values' = values

Spec == Init /\ [][Next]_values

TokenHolder(i) == values[i] = values[N]

AlwaysHasToken == <>[]<>(EXISTS i \in 1..N : TokenHolder(i))

EventuallyOneToken == []<>~(EXISTS <<i, j>> \in (1..N) \x (1..N) : 
                          TokenHolder(i) /\ TokenHolder(j) /\ i # j)

Theorem == AlwaysHasToken /\ EventuallyOneToken

Fairness == WF_vars(Next, values)
```
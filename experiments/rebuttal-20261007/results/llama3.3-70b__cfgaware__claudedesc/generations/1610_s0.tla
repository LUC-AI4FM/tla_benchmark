```
MODULE Quicksort
VARIABLES Ainit, A, S, pivot, pc

Constant N

Init ==
  /\ A = Ainit
  /\ Ainit \in [1..N -> 1..N]
  /\ S = {<<1, N>>}
  /\ pc = "Start"

qs1 ==
  /\ S # {}
  /\ \E I \in S : 
    /\ (I[2] - I[1] > 1) =>
      /\ \E piv \in I[1)..I[2] :
        /\ pivot = piv
        /\ A' = [A \X x \in DOMAIN A : 
                  IF x < piv
                  THEN <<<<\E y \in I[1]..(piv-1) : A[y] >>>> 
                  ELSE IF x > piv
                       THEN <<<<\E y \in (piv+1)..I[2] : A[y] >>>>
                       ELSE A[x]]
        /\ S' = (S \ {I}) \cup {<<I[1], piv-1>>, <<piv+1, I[2]>>}
      /\ pc' = "Pivot"
    /\ (I[2] - I[1] = 1) =>
      /\ S' = S \ {I}
      /\ A' = A
      /\ pc' = "Remove"
  /\ pc' = "Next"

Next ==
  qs1

Spec == Init /\ [][Next]_vars
Termination == <>(pc = "Done")

THEOREM Spec => []Termination
```
Note: The `qs1` action is defined using the `\E` (there exists) operator to express nondeterminism. The `A'` expression uses a lambda function (`[A \X x \in DOMAIN A : ...]`) to create a new array that satisfies the required properties.

Also note that this specification does not include an explicit sorting-correctness safety invariant, as per your request. However, in practice, you would typically want to include such an invariant to ensure that the algorithm produces a sorted output.
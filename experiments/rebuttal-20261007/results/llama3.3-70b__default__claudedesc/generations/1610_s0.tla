```tla
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES Ainit, A, S, pivot, pc

Init ==
  /\ A = Ainit
  /\ Ainit \in [1..N -> 1..N]
  /\ S = {<<1, N>>}
  /\ pivot = 0
  /\ pc = "Start"

qs1 ==
  /\ S # {}
  /\ \E I \in S : 
    /\ \E piv \in (I[1]..I[2]) :
      /\ A' = [A \X x \in Domain(A) |-> IF x \in I[1]..I[2]
        THEN IF x < piv
          THEN <<x, CHOOSE y \in I[1]..I[2] : A[y] <= A[x]>> 
          ELSE IF x > piv 
            THEN <<x, CHOOSE y \in I[1]..I[2] : A[y] >= A[x]>>
            ELSE <<x, x>>
        ELSE <<x, x>>]
      /\ S' = (S \ {I}) \cup {<<I[1], piv-1>>, <<piv+1, I[2]>>} 
      /\ pivot' = piv
  /\ pc' = "qs1"

Next ==
  /\ pc = "Start" /\ qs1
  \/ pc = "qs1" /\ S' = {} /\ pc' = "Done"
  \/ pc = "qs1" /\ S # {} /\ qs1

Spec == Init /\ [][Next]_vars
Termination == <>(pc = "Done")

THEOREM Spec => []Termination
```
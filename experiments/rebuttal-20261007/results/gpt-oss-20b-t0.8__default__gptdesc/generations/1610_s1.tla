MODULE QuickSort
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES A, S, pc

IntervalSet ==
  { <l,r> | l \in 1..N /\ r \in 1..N /\ l <= r }

Multiset(a) == [v \in 1..N -> #( { i \in 1..N : a[i] = v } ) ]

AddIntervals(i,p) ==
   LET l == i[1]; r == i[2]
   IN
      IF l <= p-1 THEN {<l, p-1>} ELSE {}
      \cup IF p+1 <= r THEN {<p+1, r>} ELSE {}

Init ==
  /\ A \in [1..N -> 1..N]
  /\ pc = "qs1"
  /\ S = {<1,N>}
  /\ S \subseteq IntervalSet
  /\ \A i \in 1..N : (A[i] \in 1..N)

qs1 ==
  \E i \in S :
     LET l == i[1]; r == i[2]
     IN
       /\ p \in 1..N /\ l <= p <= r
       /\ \E B' \in [1..N -> 1..N] :
           /\ Multiset[B'] = Multiset[A]
           /\ (\A j \in 1..N : (l <= j < p => B'[j] <= B'[p]))
           /\ (\A k \in 1..N : (p < k <= r => B'[k] >= B'[p]))
           /\ (\A j \in 1..N : (j < l \/ j > r => B'[j] = A[j]))
           /\ A' = B'
       /\ S' = (S \ {i}) ∪ AddIntervals(i,p)
       /\ pc' = "qs1"

done ==
  /\ S = {}
  /\ pc' = "Done"

Next == qs1 \/ done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
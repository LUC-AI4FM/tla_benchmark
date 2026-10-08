MODULE QuickSort
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES arr, S, pc

Perm(a,b) ==
  \A v \in 1..N :
    (# { i \mid a[i] = v }) = (# { i \mid b[i] = v })

Partition(a,l,r,p) ==
  \A i \in 1..N :
     IF l <= i /\ i <= p-1 THEN a[i] <= a[p]
     ELSE IF p+1 <= i /\ i <= r THEN a[i] > a[p]
     ELSE TRUE

IntervalSet == { <<i,j>> | i \in 1..N /\ j \in 1..N /\ i <= j }

Init ==
  /\ arr \in [1..N -> 1..N]
  /\ S = {<<1,N>>}
  /\ pc = "qs1"

qs1 ==
  /\ pc = "qs1"
  /\ (
       (S = {} /\ pc' = "Done" /\ arr' = arr /\ S' = {})
        \/
       (\E I \in S :
          LET l == I[1]
              r == I[2] IN
          (\E p \in 1..N :
             (l <= p /\ p <= r) /\
             arr' \in [1..N -> 1..N] /\ Perm(arr,arr') /\ Partition(arr',l,r,p) /\
             S' = (S \ {I}) \cup IF l <= p-1 THEN {<<l,p-1>>} ELSE {} \cup IF p+1 <= r THEN {<<p+1,r>>} ELSE {} /\
             pc' = "qs1"))
      )

Next == qs1

Inv ==
  /\ arr \in [1..N -> 1..N]
  /\ S \subseteq IntervalSet
  /\ pc \in {"qs1","Done"}

Spec == Init /\ [][Next]_vars /\ WF_vars Next

THEOREM Safe == Spec => [] Inv
THEOREM Termination == Spec => <> (pc = "Done")
===============================================================================
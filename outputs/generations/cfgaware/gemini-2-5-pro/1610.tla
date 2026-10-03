---- MODULE Quicksort ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT N
ASSUME N \in Nat /\ N > 0

VARIABLES a, S, pc

vars == <<a, S, pc>>

\* Helper operator to represent a sequence as a multiset (bag)
Bag(s) == [ x \in { s[i] : i \in DOMAIN s } |-> Cardinality({ i \in DOMAIN s : s[i] = x }) ]

\* Checks if sequence s1 is a permutation of sequence s2
IsPermutation(s1, s2) == Bag(s1) = Bag(s2)

\* Checks if the subarray arr[l..r] is partitioned around the pivot at index p
IsPartitioned(arr, l, r, p) ==
    /\ \A i \in l..(p-1) : arr[i] <= arr[p]
    /\ \A i \in (p+1)..r : arr[i] >= arr[p]

\* The initial state of the system
Init ==
    /\ pc = "qs1"
    /\ a \in [1..N -> 1..N]
    /\ S = {<<1, N>>}

\* The single action corresponding to one step of the quicksort process:
\* choose an interval, choose a pivot, and partition the subarray.
qs1 ==
    /\ pc = "qs1"
    /\ S # {}
    /\ \E l, r \in 1..N:
        /\ <<l, r>> \in S
        /\ \E p \in l..r:
            /\ \E a_new \in [1..N -> 1..N]:
                /\ IsPermutation(a_new, a)
                /\ IsPartitioned(a_new, l, r, p)
                /\ LET S_without   == S \ {<<l, r>>}
                       S_new_left  == IF l < p THEN {<<l, p-1>>} ELSE {}
                       S_new_right == IF p < r THEN {<<p+1, r>>} ELSE {}
                       S_next      == S_without \cup S_new_left \cup S_new_right
                IN /\ a' = a_new
                   /\ S' = S_next
                   /\ pc' = IF S_next = {} THEN "Done" ELSE "qs1"

\* The next-state relation
Next == qs1 \/ (pc = "Done" /\ UNCHANGED vars)

\* The main temporal specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The property that the algorithm eventually terminates
Termination == <>(pc = "Done")

====
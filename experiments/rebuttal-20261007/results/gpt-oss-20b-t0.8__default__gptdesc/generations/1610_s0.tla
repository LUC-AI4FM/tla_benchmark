MODULE QuickSortInPlace
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES A, S, pc

(* Interval record type *)
Interval == [low : 1..N, high : 1..N]

Count(v, arr) ==
    Cardinality({ i : i \in 1..N /\ arr[i] = v })

PermutationConstraint(arr1, arr2) ==
    ∀v ∈ 1..N : Count(v,arr1) = Count(v,arr2)

PartitionConstraints(arr, low, high, pivot) ==
    /\ low <= pivot
    /\ pivot <= high
    /\ ∀k ∈ low .. pivot-1 : arr[k] <= arr[pivot]
    /\ ∀k ∈ pivot+1 .. high : arr[k] >= arr[pivot]

SubIntervals(low, high, pivot) ==
    LET left  == IF pivot > low THEN {[low |-> low, high |-> pivot-1]} ELSE {}
        right == IF pivot < high THEN {[low |-> pivot+1, high |-> high]} ELSE {}
    IN left ∪ right

Init ==
    /\ A ∈ [1..N -> 1..N]
    /\ Cardinality({A[i] : i \in 1..N}) = N
    /\ S = { [low |-> 1, high |-> N] }
    /\ pc = "QS"

qsAction ==
    /\ pc = "QS"
    /\ S ≠ {}
    /\ I ∈ S
    /\ p ∈ 1..N
    /\ I.low <= p <= I.high
    /\ B ∈ [1..N -> 1..N]
    /\ PartitionConstraints(B, I.low, I.high, p)
    /\ PermutationConstraint(A,B)
    /\ A' = B
    /\ S' = (S \ {I}) ∪ SubIntervals(I.low, I.high, p)
    /\ pc' = "QS"

terminateAction ==
    /\ pc = "QS"
    /\ S = {}
    /\ A' = A
    /\ S' = S
    /\ pc' = "Done"

Next == qsAction \/ terminateAction

PermInv ==
    /\ A ∈ [1..N -> 1..N]
    /\ Cardinality({A[i] : i \in 1..N}) = N

Spec == Init
       /\ [][Next]_<<A,S,pc>>
       /\ WF_action(Next)
       /\ []PermInv
       /\ <> (pc = "Done")
MODULE QuickSort
EXTENDS Sequences, FiniteSets

CONSTANT N

VARIABLES array, intervals

(* Helper definitions *)

BijectiveOn(f, l, r) ==
    /\ f ∈ [l..r -> l..r]
    /\ (∀ x,y ∈ l..r : f[x] = f[y] => x=y)
    /\ Range(f) = {l..r}

PermutationWithin(arr, arr', l, r) ==
    ∃ f ∈ [l..r -> l..r] :
        /\ (∀ i ∈ 1..N : (i < l \/ i > r) => arr'[i] = arr[i])
        /\ (∀ i ∈ l..r : arr'[i] = arr[f[i]])
        /\ BijectiveOn(f, l, r)

PartitionCondition(arr', l, r, p) ==
    LET maxLeft == IF p = l THEN 0 ELSE MAX(arr'[l .. p-1]) IN
        LET minRight == IF p = r THEN N+1 ELSE MIN(arr'[p+1 .. r]) IN
            maxLeft <= minRight

(* Initial state *)

Init ==
    /\ array ∈ [1..N -> 1..N]
    /\ intervals = {<<1,N>>}

(* Next-state relation *)

Next ==
    ∃ i ∈ intervals :
        LET l == i[1] ; r == i[2] IN
            (r - l + 1 <= 1) =>
                /\ array' = array
                /\ intervals' = intervals \ {i}
            \/ (r - l + 1 > 1) =>
                ∃ p ∈ l..r :
                    ∃ arr' ∈ [1..N -> 1..N] :
                        /\ PermutationWithin(array, arr', l, r)
                        /\ PartitionCondition(arr', l, r, p)
                        /\ array' = arr'
                        /\ intervals' = (intervals \ {i}) ∪ {<<l,p-1>>, <<p+1,r>>}

(* Specification *)

Spec == Init /\ [][Next]_vars

(* Liveness property: eventual termination *)

Termination == []<>(intervals = {})

END QuickSort
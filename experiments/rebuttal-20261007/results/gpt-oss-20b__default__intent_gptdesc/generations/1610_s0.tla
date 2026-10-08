MODULE QuickSort

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, DOMAIN, OrigArr

(* Type definitions *)
Index == 1..N
Intervals == { <<lo, hi>> | lo \in Index /\ hi \in Index /\ lo <= hi }

VARIABLES arr, pending

Init ==
    arr = OrigArr /\
    pending = { <<1,N>> }

TypeInv ==
    arr ∈ Seq(DOMAIN) /\ Len(arr)=N /\
    pending ⊆ Intervals

Count(v, seq) == Len({ i \in 1..Len(seq) : seq[i] = v })

Permutation(s1,s2) == ∀ v \in DOMAIN : Count(v,s1)=Count(v,s2)

SubSeqPermute(arr, lo, hi, newArr) ==
    Permutation(newArr[lo .. hi], arr[lo .. hi])

Sorted == ∀ i,j \in 1..N : (i < j) => arr[i] <= arr[j]

PartitionAction ==
    ∃ t \in pending :
        LET lo == t[1], hi == t[2] IN
            lo < hi /\ 
            ∃ p \in {lo .. hi-1} :
                ∃ newArr \in Seq(DOMAIN) :
                    Len(newArr)=N /\
                    (∀ i \in 1..N : (i < lo \/ i > hi) => newArr[i] = arr[i]) /\
                    SubSeqPermute(arr, lo, hi, newArr) /\
                    (∀ i,j \in 1..N :
                        (lo <= i /\ i <= p /\ p+1 <= j /\ j <= hi) => newArr[i] <= newArr[j]) ) /\
            pending' = pending \ { t } ∪ { <<lo,p>>, <<p+1,hi>> } /\
            arr' = newArr

RemoveAction ==
    ∃ t \in pending :
        LET lo == t[1], hi == t[2] IN
            lo >= hi /\ 
            pending' = pending \ { t } /\ arr' = arr

Next == PartitionAction \/ RemoveAction

Spec == Init /\ [][Next]_<<arr,pending>> /\ WF_<<arr,pending>>(Next)

SafetyInvariant == TypeInv /\ Permutation(arr, OrigArr)

OrderingProgress == [] (pending = {} => Sorted)

Liveness == <> (pending = {})

END QuickSort
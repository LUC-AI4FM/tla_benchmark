-------------------------------- MODULE Quicksort --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0

VARIABLES arr, arr0, pc, stack, lo, hi

vars == <<arr, arr0, pc, stack, lo, hi>>

\* Helper: Set of all permutations of a sequence
PermutationsOf(s) ==
    LET Domain == 1..Len(s)
        Range == {s[i] : i \in Domain}
    IN {f \in [Domain -> Range] : 
        /\ \A i, j \in Domain : i # j => f[i] # f[j] \/ 
           (Cardinality({k \in Domain : s[k] = s[i]}) > 1)
        /\ \A v \in Range : Cardinality({i \in Domain : f[i] = v}) = 
                           Cardinality({i \in Domain : s[i] = v})}

\* Check if sequence is sorted
IsSorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Check if two sequences are permutations of each other
IsPermutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in Int : Cardinality({i \in 1..Len(s1) : s1[i] = v}) = 
                      Cardinality({i \in 1..Len(s2) : s2[i] = v})

\* Subarray from index l to h
SubArray(a, l, h) == [i \in 1..(h-l+1) |-> a[l+i-1]]

\* Check if partitioned: all elements in lo..pivot <= all elements in pivot+1..hi
IsPartitioned(a, l, pivot, h) ==
    \A i \in l..pivot, j \in (pivot+1)..h : a[i] <= a[j]

\* Generate all valid partitioned permutations of subarray
PartitionedPerms(a, l, h, pivot) ==
    LET subLen == h - l + 1
        indices == l..h
        \* All permutations of values in the subarray
        subVals == [i \in 1..subLen |-> a[l+i-1]]
    IN {newArr \in [1..ArrayLen -> Int] :
        \* Preserve elements outside subarray
        /\ \A i \in 1..ArrayLen : (i < l \/ i > h) => newArr[i] = a[i]
        \* Subarray is a permutation of original subarray
        /\ IsPermutation(SubArray(newArr, l, h), subVals)
        \* Subarray is partitioned around pivot position
        /\ IsPartitioned(newArr, l, pivot, h)}

\* Initial state
Init ==
    /\ arr \in [1..ArrayLen -> 1..ArrayLen]  \* Array with values 1..ArrayLen
    /\ arr0 = arr                             \* Save initial array
    /\ pc = "Start"
    /\ stack = <<>>
    /\ lo = 1
    /\ hi = ArrayLen

\* Start the algorithm - push initial call
Start ==
    /\ pc = "Start"
    /\ IF ArrayLen >= 1
       THEN /\ pc' = "QS"
            /\ lo' = 1
            /\ hi' = ArrayLen
       ELSE /\ pc' = "Done"
            /\ lo' = lo
            /\ hi' = hi
    /\ UNCHANGED <<arr, arr0, stack>>

\* QS procedure entry - check if work needed
QSEntry ==
    /\ pc = "QS"
    /\ IF lo >= hi
       THEN \* Base case: return
            IF stack = <<>>
            THEN /\ pc' = "Done"
                 /\ UNCHANGED <<lo, hi, stack>>
            ELSE /\ pc' = Head(stack).returnPC
                 /\ lo' = Head(stack).lo
                 /\ hi' = Head(stack).hi
                 /\ stack' = Tail(stack)
       ELSE \* Need to partition
            /\ pc' = "Partition"
            /\ UNCHANGED <<lo, hi, stack>>
    /\ UNCHANGED <<arr, arr0>>

\* Partition: choose pivot and rearrange
Partition ==
    /\ pc = "Partition"
    /\ \E pivot \in lo..hi :
        \E newArr \in PartitionedPerms(arr, lo, hi, pivot) :
            /\ arr' = newArr
            /\ pc' = "RecurseLeft"
            /\ stack' = Append(stack, [returnPC |-> "RecurseRight", 
                                        lo |-> lo, 
                                        hi |-> hi,
                                        pivot |-> pivot])
            /\ hi' = pivot - 1
            /\ UNCHANGED lo
    /\ UNCHANGED arr0

\* After left recursion, do right recursion
RecurseLeft ==
    /\ pc = "RecurseLeft"
    /\ pc' = "QS"
    /\ UNCHANGED <<arr, arr0, stack, lo, hi>>

\* Setup right recursion
RecurseRight ==
    /\ pc = "RecurseRight"
    /\ IF stack = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<lo, hi, stack>>
       ELSE LET frame == Head(stack)
            IN /\ lo' = frame.pivot + 1
               /\ hi' = frame.hi
               /\ stack' = Tail(stack)
               /\ pc' = "QS"
    /\ UNCHANGED <<arr, arr0>>

\* Alternative simpler model for partition
SimplePartition ==
    /\ pc = "Partition"
    /\ lo < hi
    /\ \E pivot \in lo..hi :
        \E perm \in [lo..hi -> lo..hi] :
            /\ \A i, j \in lo..hi : i # j => perm[i] # perm[j]  \* bijection
            /\ LET newArr == [i \in 1..ArrayLen |-> 
                              IF i \in lo..hi THEN arr[perm[i]] ELSE arr[i]]
               IN /\ IsPartitioned(newArr, lo, pivot, hi)
                  /\ arr' = newArr
                  /\ pc' = "AfterPartition"
                  /\ stack' = Append(stack, [lo |-> lo, hi |-> hi, pivot |-> pivot])
                  /\ UNCHANGED <<lo, hi>>
    /\ UNCHANGED arr0

AfterPartition ==
    /\ pc = "AfterPartition"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN /\ lo' = frame.lo
          /\ hi' = frame.pivot - 1
          /\ pc' = "LeftRecurse"
          /\ UNCHANGED stack
    /\ UNCHANGED <<arr, arr0>>

LeftRecurse ==
    /\ pc = "LeftRecurse"
    /\ IF lo >= hi
       THEN /\ pc' = "PrepareRight"
            /\ UNCHANGED <<lo, hi, stack>>
       ELSE /\ pc' = "Partition"
            /\ UNCHANGED <<lo, hi, stack>>
    /\ UNCHANGED <<arr, arr0>>

PrepareRight ==
    /\ pc = "PrepareRight"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN /\ lo' = frame.pivot + 1
          /\ hi' = frame.hi
          /\ stack' = Tail(stack)
          /\ pc' = "RightRecurse"
    /\ UNCHANGED <<arr, arr0>>

RightRecurse ==
    /\ pc = "RightRecurse"
    /\ IF lo >= hi
       THEN IF stack = <<>>
            THEN /\ pc' = "Done"
                 /\ UNCHANGED <<lo, hi, stack>>
            ELSE /\ pc' = "PrepareRight"
                 /\ UNCHANGED <<lo, hi, stack>>
       ELSE /\ pc' = "Partition"
            /\ UNCHANGED <<lo, hi, stack>>
    /\ UNCHANGED <<arr, arr0>>

\* Simplified complete Next relation
DoPartition ==
    /\ pc = "Partition"
    /\ lo < hi
    /\ \E pivotIdx \in lo..hi :
        /\ \E newArr \in [1..ArrayLen -> Int] :
            \* Elements outside lo..hi unchanged
            /\ \A i \in 1..ArrayLen : (i < lo \/ i > hi) => newArr[i] = arr[i]
            \* Same multiset of values in lo..hi
            /\ \A v \in Int : 
                Cardinality({i \in lo..hi : newArr[i] = v}) = 
                Cardinality({i \in lo..hi : arr[i] = v})
            \* Partitioned around pivotIdx
            /\ \A i \in lo..pivotIdx : \A j \in (pivotIdx+1)..hi : 
                newArr[i] <= newArr[j]
            /\ arr' = newArr
            /\ stack' = Append(stack, [lo |-> lo, hi |-> hi, piv |-> pivotIdx])
            /\ hi' = pivotIdx - 1
            /\ pc' = "Partition"
            /\ UNCHANGED <<arr0, lo>>

ReturnFromPartition ==
    /\ pc = "Partition"
    /\ lo >= hi
    /\ IF stack = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<lo, hi, stack>>
       ELSE LET frame == Head(stack)
            IN IF frame.piv < frame.hi
               THEN \* Go to right subtree
                    /\ lo' = frame.piv + 1
                    /\ hi' = frame.hi
                    /\ stack' = Append(Tail(stack), 
                                [lo |-> frame.lo, hi |-> frame.hi, piv |-> frame.hi + 1])
                    /\ pc' = "Partition"
               ELSE \* Right subtree done, pop
                    /\ stack' = Tail(stack)
                    /\ pc' = "Partition"
                    /\ UNCHANGED <<lo, hi>>
    /\ UNCHANGED <<arr, arr0>>

Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ DoPartition
    \/ ReturnFromPartition
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: array is always a permutation of initial array
PermutationInvariant ==
    IsPermutation(arr, arr0)

\* Type invariant
TypeInvariant ==
    /\ arr \in [1..ArrayLen -> Int]
    /\ arr0 \in [1..ArrayLen -> Int]
    /\ pc \in {"Start", "Partition", "Done"}
    /\ lo \in 1..(ArrayLen+1)
    /\ hi \in 0..ArrayLen

\* Termination property
Termination == <>(pc = "Done")

\* Final correctness: when done, array is sorted and is permutation of original
FinalCorrectness ==
    pc = "Done" => (IsSorted(arr) /\ IsPermutation(arr, arr0))

================================================================================
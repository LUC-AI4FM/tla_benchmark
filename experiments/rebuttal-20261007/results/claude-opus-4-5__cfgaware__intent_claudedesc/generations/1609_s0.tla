---------------------------- MODULE quicksort ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT ArrayLen

VARIABLES array, stack, done, originalArray

vars == <<array, stack, done, originalArray>>

Index == 1..ArrayLen
Value == 1..ArrayLen

PermutationsOf(S) ==
    LET perms[T \in SUBSET S] ==
        IF T = {} THEN {<<>>}
        ELSE UNION { {<<x>> \o p : p \in perms[T \ {x}]} : x \in T }
    IN perms[S]

IsPermutationOf(arr1, arr2, lo, hi) ==
    LET Range == lo..hi
        Vals1 == [i \in Range |-> arr1[i]]
        Vals2 == [i \in Range |-> arr2[i]]
        Bag1 == [v \in Value |-> Cardinality({i \in Range : arr1[i] = v})]
        Bag2 == [v \in Value |-> Cardinality({i \in Range : arr2[i] = v})]
    IN Bag1 = Bag2

IsValidPartition(oldArr, newArr, lo, hi, pivotIdx) ==
    /\ pivotIdx \in lo..hi
    /\ IsPermutationOf(oldArr, newArr, lo, hi)
    /\ \A i \in lo..(pivotIdx-1) : newArr[i] <= newArr[pivotIdx]
    /\ \A i \in (pivotIdx+1)..hi : newArr[i] >= newArr[pivotIdx]
    /\ \A i \in Index \ (lo..hi) : newArr[i] = oldArr[i]

IsSorted(arr) ==
    \A i, j \in Index : i < j => arr[i] <= arr[j]

IsGlobalPermutation(arr1, arr2) ==
    LET Bag1 == [v \in Value |-> Cardinality({i \in Index : arr1[i] = v})]
        Bag2 == [v \in Value |-> Cardinality({i \in Index : arr2[i] = v})]
    IN Bag1 = Bag2

TypeOK ==
    /\ array \in [Index -> Value]
    /\ stack \in SUBSET (Index \X Index)
    /\ done \in BOOLEAN
    /\ originalArray \in [Index -> Value]

Init ==
    /\ array \in [Index -> Value]
    /\ originalArray = array
    /\ stack = IF ArrayLen >= 1 THEN {<<1, ArrayLen>>} ELSE {}
    /\ done = FALSE

PartitionStep ==
    /\ ~done
    /\ stack /= {}
    /\ \E task \in stack :
        LET lo == task[1]
            hi == task[2]
        IN
        IF lo >= hi
        THEN
            /\ stack' = stack \ {task}
            /\ array' = array
            /\ done' = (stack' = {})
            /\ originalArray' = originalArray
        ELSE
            \E pivotIdx \in lo..hi :
            \E newArr \in [Index -> Value] :
                /\ IsValidPartition(array, newArr, lo, hi, pivotIdx)
                /\ array' = newArr
                /\ LET leftTask == IF pivotIdx > lo THEN {<<lo, pivotIdx - 1>>} ELSE {}
                       rightTask == IF pivotIdx < hi THEN {<<pivotIdx + 1, hi>>} ELSE {}
                   IN stack' = (stack \ {task}) \cup leftTask \cup rightTask
                /\ done' = (stack' = {})
                /\ originalArray' = originalArray

Finish ==
    /\ ~done
    /\ stack = {}
    /\ done' = TRUE
    /\ UNCHANGED <<array, stack, originalArray>>

Next ==
    \/ PartitionStep
    \/ Finish

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(done = TRUE)

Safety ==
    done => (IsSorted(array) /\ IsGlobalPermutation(array, originalArray))

==========================================================================
---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES
    array,          \* The array being sorted (function from 1..N to Int)
    initialArray,   \* Snapshot of initial array for permutation checking
    tasks,          \* Set of pending tasks: sort tasks and merge tasks
    done            \* Boolean indicating algorithm completion

\* Task types:
\* Sort task: [type |-> "sort", lo |-> l, hi |-> h]
\* Merge task: [type |-> "merge", lo |-> l, mid |-> m, hi |-> h, 
\*              leftSorted |-> TRUE/FALSE, rightSorted |-> TRUE/FALSE]

vars == <<array, initialArray, tasks, done>>

-----------------------------------------------------------------------------
\* Helper: Check if a range is sorted
IsSortedRange(arr, lo, hi) ==
    \A i, j \in lo..hi : i < j => arr[i] <= arr[j]

\* Helper: Multiset (bag) of elements in array
ArrayBag(arr) ==
    [v \in UNION {arr[i] : i \in DOMAIN arr} |-> 
        Cardinality({i \in DOMAIN arr : arr[i] = v})]

\* Helper: Compare bags for equality
BagsEqual(b1, b2) ==
    DOMAIN b1 = DOMAIN b2 /\ \A v \in DOMAIN b1 : b1[v] = b2[v]

\* Helper: Multiset of range
RangeBag(arr, lo, hi) ==
    LET indices == {i \in lo..hi : TRUE}
        values == {arr[i] : i \in indices}
    IN [v \in values |-> Cardinality({i \in indices : arr[i] = v})]

\* Helper: Merge two sorted subarrays arr[lo..mid] and arr[mid+1..hi]
\* Returns a sequence representing the merged result
MergeArrays(arr, lo, mid, hi) ==
    LET left == [i \in 1..(mid - lo + 1) |-> arr[lo + i - 1]]
        right == [i \in 1..(hi - mid) |-> arr[mid + i]]
        
        RECURSIVE MergeSeqs(_, _, _)
        MergeSeqs(l, r, acc) ==
            IF l = <<>> /\ r = <<>>
            THEN acc
            ELSE IF l = <<>>
            THEN acc \o r
            ELSE IF r = <<>>
            THEN acc \o l
            ELSE IF Head(l) <= Head(r)
            THEN MergeSeqs(Tail(l), r, Append(acc, Head(l)))
            ELSE MergeSeqs(l, Tail(r), Append(acc, Head(r)))
    IN MergeSeqs([i \in 1..Len(left) |-> left[i]], 
                 [i \in 1..Len(right) |-> right[i]], 
                 <<>>)

\* Convert sequence to function for array update
SeqToFunc(seq, offset) ==
    [i \in offset..(offset + Len(seq) - 1) |-> seq[i - offset + 1]]

-----------------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ array \in [1..N -> Int]
    /\ initialArray \in [1..N -> Int]
    /\ done \in BOOLEAN
    /\ tasks \subseteq (
        [type: {"sort"}, lo: 1..N, hi: 1..N] \cup
        [type: {"merge"}, lo: 1..N, mid: 1..N, hi: 1..N])

\* Initial state: array can have any integer values
Init ==
    /\ array \in [1..N -> Int]
    /\ initialArray = array
    /\ tasks = {[type |-> "sort", lo |-> 1, hi |-> N]}
    /\ done = FALSE

-----------------------------------------------------------------------------
\* Action: Handle a sort task by either marking range as sorted (base case)
\* or splitting into two sort tasks (divide step)

\* Base case: single element or empty range is already sorted
SortBase(task) ==
    /\ task \in tasks
    /\ task.type = "sort"
    /\ task.hi <= task.lo
    /\ tasks' = tasks \ {task}
    /\ UNCHANGED <<array, initialArray, done>>

\* Divide: split into two halves and schedule merge after both complete
SortDivide(task) ==
    /\ task \in tasks
    /\ task.type = "sort"
    /\ task.hi > task.lo
    /\ LET mid == task.lo + ((task.hi - task.lo) \div 2)
           leftTask == [type |-> "sort", lo |-> task.lo, hi |-> mid]
           rightTask == [type |-> "sort", lo |-> mid + 1, hi |-> task.hi]
           mergeTask == [type |-> "merge", lo |-> task.lo, mid |-> mid, hi |-> task.hi]
       IN tasks' = (tasks \ {task}) \cup {leftTask, rightTask, mergeTask}
    /\ UNCHANGED <<array, initialArray, done>>

\* Merge: combine two sorted halves (only when no pending sorts for this range)
\* A merge can execute when there are no sort tasks whose range is contained in the merge range
CanMerge(mergeTask) ==
    ~\E t \in tasks :
        /\ t.type = "sort"
        /\ t.lo >= mergeTask.lo
        /\ t.hi <= mergeTask.hi

DoMerge(task) ==
    /\ task \in tasks
    /\ task.type = "merge"
    /\ CanMerge(task)
    /\ LET merged == MergeArrays(array, task.lo, task.mid, task.hi)
           newArray == [i \in 1..N |-> 
                         IF i >= task.lo /\ i <= task.hi
                         THEN merged[i - task.lo + 1]
                         ELSE array[i]]
       IN array' = newArray
    /\ tasks' = tasks \ {task}
    /\ UNCHANGED <<initialArray, done>>

\* Completion: all tasks done
Complete ==
    /\ tasks = {}
    /\ done = FALSE
    /\ done' = TRUE
    /\ UNCHANGED <<array, initialArray, tasks>>

-----------------------------------------------------------------------------
\* Next state relation
Next ==
    \/ \E task \in tasks : SortBase(task)
    \/ \E task \in tasks : SortDivide(task)
    \/ \E task \in tasks : DoMerge(task)
    \/ Complete

\* Fairness: all enabled actions eventually execute
Fairness ==
    /\ \A task \in [type: {"sort"}, lo: 1..N, hi: 1..N] :
        WF_vars(SortBase(task))
    /\ \A task \in [type: {"sort"}, lo: 1..N, hi: 1..N] :
        WF_vars(SortDivide(task))
    /\ \A task \in [type: {"merge"}, lo: 1..N, mid: 1..N, hi: 1..N] :
        WF_vars(DoMerge(task))
    /\ WF_vars(Complete)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: When done, array is sorted
Sorted ==
    done => \A i, j \in 1..N : i < j => array[i] <= array[j]

\* Safety: Array is always a permutation of initial array
\* We express this by checking multiset equality
Permutation ==
    \A v \in UNION {{array[i] : i \in 1..N}, {initialArray[i] : i \in 1..N}} :
        Cardinality({i \in 1..N : array[i] = v}) = 
        Cardinality({i \in 1..N : initialArray[i] = v})

\* Combined safety invariant
Safety == Sorted /\ Permutation

\* Liveness: Algorithm eventually terminates
Termination == <>done

-----------------------------------------------------------------------------
\* Merge correctness theorem (expressed as an invariant property)
\* When a merge completes, the result is sorted and preserves elements

MergeCorrectness ==
    \A lo, mid, hi \in 1..N :
        /\ lo <= mid
        /\ mid < hi
        /\ IsSortedRange(array, lo, mid)
        /\ IsSortedRange(array, mid + 1, hi)
        => LET merged == MergeArrays(array, lo, mid, hi)
           IN /\ \A i, j \in 1..Len(merged) : i < j => merged[i] <= merged[j]
              /\ Cardinality({i \in 1..Len(merged) : merged[i] = v}) =
                 Cardinality({i \in lo..hi : array[i] = v})
                 \* for all v in the range

=============================================================================
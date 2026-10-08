MODULE QuickSort
EXTENDS Naturals, Sequences

CONSTANTS ArrayLen, InitArray \* Assume InitArray is a sequence of Nat of length ArrayLen

VARIABLES A, stack, pc

\* Frame record type
Frame == [low: Nat, high: Nat]

\* Helper functions
Count(arr, v) ==
    \# { i \in 0 .. ArrayLen-1 : arr[i] = v }

CountSub(arr, low, high, v) ==
    \# { i \in low .. high : arr[i] = v }

MultisetEqual(arr1, arr2) ==
    \A v \in Nat : Count(arr1, v) = Count(arr2, v)

Permute(arr, newArr, low, high) ==
    (\A i \in 0 .. ArrayLen-1 :
        (i < low \/ i > high => newArr[i] = arr[i])) /\
    (\A v \in Nat : CountSub(arr, low, high, v) = CountSub(newArr, low, high, v))

Partitioned(arr, low, high) ==
    \E p \in low .. high :
        \A i \in low .. p
            \A j \in (p+1) .. high :
                arr[i] <= arr[j]

\* Invariants
PermutationInv == MultisetEqual(A, InitArray)

SortedArr == \A i \in 0 .. ArrayLen-2 : A[i] <= A[i+1]

SortedInv == pc = "Done" => SortedArr

SafetyInv == PermutationInv /\ SortedInv

vars == <<A, stack, pc>>

\* Initial state
Init ==
    /\ A = InitArray
    /\ stack = << [low -> 0, high -> ArrayLen - 1] >>
    /\ pc = "Loop"

\* Actions
ProcessEmptyFrame ==
    /\ pc = "Loop"
    /\ Len(stack) > 0
    /\ LET f == Last(stack)
       restStack == SubSeq(stack, 1, Len(stack)-1)
      IN
        /\ f.low >= f.high
        /\ stack' = restStack
        /\ A' = A
        /\ pc' = "Loop"

PartitionStep ==
    /\ pc = "Loop"
    /\ Len(stack) > 0
    /\ LET f == Last(stack)
       restStack == SubSeq(stack, 1, Len(stack)-1)
      IN
        /\ f.low < f.high
        /\ \E p \in f.low .. f.high :
            \E newA \in Seq(Nat) :
                /\ Permute(A, newA, f.low, f.high)
                /\ Partitioned(newA, f.low, f.high)
                /\ stack' = restStack ^ [[ [low -> f.low, high -> p], [low -> p+1, high -> f.high] ]]
                /\ A' = newA
        /\ pc' = "Loop"

Finish ==
    /\ pc = "Loop"
    /\ Len(stack) = 0
    /\ pc' = "Done"
    /\ stack' = <<>>
    /\ A' = A

Next == ProcessEmptyFrame \/ PartitionStep \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => []SafetyInv
THEOREM Spec => <> (pc = "Done")
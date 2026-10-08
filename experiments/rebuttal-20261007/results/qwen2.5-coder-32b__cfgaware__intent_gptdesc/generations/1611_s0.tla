------------------------------- MODULE MergeSortSpec -------------------------------

CONSTANTS
    \* The length of the array to be sorted.
    ArrayLen,

    \* Default initial value for elements in the array (not used in this spec).
    defaultInitValue

VARIABLES
    \* The array being sorted, represented as a sequence of integers.
    array,
    
    \* A stack to manage recursive calls. Each element is a tuple (start, end) representing the subarray bounds.
    callStack,

    \* A temporary storage for merging two halves.
    tempStorage

\* Define the initial state where the array can be any sequence of integers of length ArrayLen
Init == 
    /\ array \in [1..ArrayLen -> Int]
    /\ callStack = <<1, ArrayLen>>
    /\ tempStorage = <<>>

\* The recursive merge sort algorithm is modeled using a stack to manage subarray bounds.
Next ==
    \/ /\ callStack /= <<>>  \* If there are subarrays to process
       /\ LET (start, end) == CALL StackTop(callStack)
          IN /\ IF start < end THEN
                  LET mid == (start + end) DIV 2
                  IN /\ callStack' = Push(callStack, <<mid+1, end>>) \* Schedule right half for later processing
                     /\ callStack' = Push(callStack', <<start, mid>>) \* Process left half next
              ELSE
                  /\ callStack' = Pop(callStack) \* No more work on this subarray, return to previous level
          ELSE UNCHANGED callStack
    \/ /\ callStack /= <<>>  \* If there are subarrays to merge
       /\ LET (start1, end1) == CALL StackTop(callStack)
          IN /\ IF start1 < end1 THEN
                  LET mid == (start1 + end1) DIV 2
                      left == SubSeq(array, start1, mid)
                      right == SubSeq(array, mid+1, end1)
                      merged == Merge(left, right)
                  IN /\ array' = [array EXCEPT ![start1..end1] = merged]
                     /\ callStack' = Pop(callStack) \* Merged this subarray, return to previous level
              ELSE UNCHANGED array
    \/ UNCHANGED <<array, callStack>>

\* The merge operator combines two sorted sequences into a single sorted sequence.
Merge(left, right) ==
    LET recMerge(l, r, acc) ==
            IF l = <<>> THEN Append(acc, r)
            [] r = <<>> THEN Append(acc, l)
            [] l[1] <= r[1] THEN recMerge(Tail(l), r, Append(acc, <<l[1]>>))
            ELSE recMerge(l, Tail(r), Append(acc, <<r[1]>>))
    IN recMerge(left, right, <<>>)

\* The stack operations used to manage subarray bounds.
StackTop(stack) == Head(stack)
Push(stack, elem) == Append(stack, <<elem>>)
Pop(stack) == [stack EXCEPT ![1..Len(stack)-1] = SubSeq(stack, 2, Len(stack))]

\* The specification of the system is defined by Init and Next
Spec ==
    /\ Init
    /\ [][Next]_<<array, callStack>>

\* Termination condition: when the call stack is empty, sorting is complete.
Termination ==
    \/ callStack = <<>>  \* No more subarrays to process

\* Invariant: The array remains a permutation of its initial state throughout execution.
Invariant ==
    LET initialArray == CHOOSE init : Init /\ array = init
    IN Multiset(array) = Multiset(initialArray)

=============================================================================
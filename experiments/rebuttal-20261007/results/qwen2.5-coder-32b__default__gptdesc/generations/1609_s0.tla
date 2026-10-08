------------------------------- MODULE QuickSortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES arr, pc, stack, lo, hi, pivot, i, j

Init == 
  /\ arr \in [1..ArrayLen -> Nat]
  /\ pc = "Start"
  /\ stack = << >>
  /\ lo = 1
  /\ hi = ArrayLen
  /\ UNCHANGED <<i, j, pivot>>

QSFrame(lo_, hi_) == [lo |-> lo_, hi |-> hi_]

Next ==
  \/ /\ pc = "Start"
     /\ stack = << >>
     /\ lo = 1
     /\ hi = ArrayLen
     /\ pc' = "Partition"
  \/ /\ pc = "Partition"
     /\ lo <= hi
     /\ pivot \in {lo..hi}
     /\ i' = lo - 1
     /\ j' = hi + 1
     /\ pc' = "InnerLoop"
  \/ /\ pc = "InnerLoop"
     /\ i' < j'
     /\ \/ /\ arr[i'+1] <= arr[pivot]
            /\ i'' = i' + 1
            /\ j'' = j'
            /\ pc' = "InnerLoop"
          \/ /\ arr[j'-1] > arr[pivot]
             /\ i'' = i'
             /\ j'' = j' - 1
             /\ pc' = "InnerLoop"
          \/ /\ arr[i'+1] > arr[pivot]
             /\ arr[j'-1] <= arr[pivot]
             /\ LET temp = arr[i'+1] IN
                /\ arr' = [arr EXCEPT ![i'+1] = arr[j'-1], ![j'-1] = temp]
                /\ i'' = i' + 1
                /\ j'' = j' - 1
                /\ pc' = "InnerLoop"
     \/ /\ i' >= j'
        /\ pc' = "AfterPartition"
  \/ /\ pc = "AfterPartition"
     /\ LET temp = arr[pivot] IN
        /\ arr' = [arr EXCEPT ![pivot] = arr[j'], ![j'] = temp]
        /\ pivot' = j'
        /\ \/ /\ j' - lo > 0
               /\ stack' = Append(stack, QSFrame(lo, pivot'-1))
               /\ pc' = "CallQS"
           \/ /\ hi - j' > 0
              /\ stack' = Append(stack, QSFrame(pivot'+1, hi))
              /\ pc' = "CallQS"
           \/ /\ stack = << >>
              /\ pc' = "Done"
     \/ /\ pc = "CallQS"
        /\ LET frame = Head(stack) IN
           /\ lo' = frame.lo
           /\ hi' = frame.hi
           /\ stack' = Tail(stack)
           /\ pc' = "Partition"

Spec ==
  Init /\ [][Next]_<<arr, pc, stack, lo, hi, pivot, i, j>> /\ WF_[Next]_<<arr, pc, stack, lo, hi, pivot, i, j>>

Termination == <>[](pc = "Done")

Sorted(subarray) ==
  \A i \in 1..Len(subarray)-1 : subarray[i] <= subarray[i+1]

Permutation(seq1, seq2) ==
  /\ Len(seq1) = Len(seq2)
  /\ \A x \in DOMAIN seq1 : Cardinality({y \in DOMAIN seq2 : seq2[y] = seq1[x]}) = 1

FinalTest ==
  /\ pc = "Done"
  /\ Sorted(arr[lo..hi])
  /\ Permutation(arr[1..ArrayLen], [1..ArrayLen -> arr[1..ArrayLen]])

=============================================================================
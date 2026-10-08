MODULE MergeSort
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, ElemSet  \* ElemSet ⊆ Nat

VARIABLES arr, stack

\* Helper predicates
Low(f) == f.low
High(f) == f.high

Top(s) == IF Len(s)=0 THEN <<>> ELSE Last(s)

Init ==
  /\ arr ∈ [1..N -> ElemSet]
  /\ stack = <<[low |-> 1, high |-> N]>>

SplitAction ==
  /\ Len(stack) > 0
  /\ Low(Top(stack)) < High(Top(stack))
  /\ LET mid == (Low(Top(stack))+High(Top(stack))) \div 2 IN
        stack' = SubSeq(stack,1,Len(stack)-1)
          \/ <<[low |-> Low(Top(stack)), high |-> mid]>> 
          \/ <<[low |-> mid+1, high |-> High(Top(stack))]>
  /\ UNCHANGED arr

PopAction ==
  /\ Len(stack) > 0
  /\ Low(Top(stack)) >= High(Top(stack))
  /\ stack' = SubSeq(stack,1,Len(stack)-1)
  /\ UNCHANGED arr

Next == SplitAction \/ PopAction

Spec == Init /\ [][Next]_<<arr,stack>> /\ WF_vars({arr,stack})

\* Safety invariant: when the call stack is empty, the array is sorted
SortedFinal ==
  IF Len(stack)=0 THEN
    \A i,j ∈ 1..N : i < j => arr[i] ≤ arr[j]
  ELSE TRUE

Safety == [] SortedFinal

Spec == Spec /\ Safety

=============================================================================
END MODULE

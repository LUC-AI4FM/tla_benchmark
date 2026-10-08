MODULE QuickSort
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen, InitialArray
ASSUME ArrayLen = Len(InitialArray)

VARIABLE arr, pc, stack

Frame == [low : 1..ArrayLen, high : 1..ArrayLen]
Top(stack) == IF Len(stack)=0 THEN [low |-> 0, high |-> 0] ELSE stack[Len(stack)]

Partition(arr, low, high, p, arr') ==
  /\ (\A i \in 1..ArrayLen :
        (i < low \/ i > high) => arr'[i] = arr[i])
  /\ Sort([arr'[i] : i \in low .. high]) =
     Sort([arr[i] : i \in low .. high])
  /\ (\A i \in low .. p-1 : arr'[i] <= arr'[p])
  /\ (\A i \in p+1 .. high : arr'[i] >= arr'[p])

PermInvariant == Sort([arr[i] : i \in 1..ArrayLen]) = Sort(InitialArray)

Sorted(a) == \A i,j \in 1..ArrayLen : i < j => a[i] <= a[j]
SortedInvariant == Sorted(arr)

Init ==
  /\ arr = InitialArray
  /\ pc = "Init"
  /\ stack = <<>>

Next ==
  \/ (* Final state stays *)
     /\ pc = "Done"
     /\ arr' = arr
     /\ stack' = stack
  \/ (* Empty stack: finish sorting *)
     /\ Len(stack) = 0
     /\ pc' = "Done"
     /\ arr' = arr
     /\ stack' = <<>>
  \/ (* Pop finished frame *)
     /\ Len(stack) > 0
     /\ LET f == Top(stack)
        low == f.low
        high == f.high
       IN
          /\ low > high
          /\ pc' = "Running"
          /\ arr' = arr
          /\ stack' == SubSeq(stack, 1 .. Len(stack)-1)
  \/ (* Process active frame *)
     /\ Len(stack) > 0
     /\ LET f == Top(stack)
        low == f.low
        high == f.high
       IN
          /\ low <= high
          /\ p \in low .. high
          /\ Partition(arr, low, high, p, arr')
          /\ pc' = "Running"
          /\ newStack1 == SubSeq(stack, 1 .. Len(stack)-1)
          /\ pushL == IF low <= p-1 THEN <<[low |-> low, high |-> p-1]>> ELSE <<>>
          /\ pushR == IF p+1 <= high THEN <<[low |-> p+1, high |-> high]>> ELSE <<>>
          /\ stack' == newStack1 \cat pushL \cat pushR

Spec ==
  Init /\ [][Next]_<<arr, pc, stack>> \/ WF_vars(Next)

SafetyInvariant == PermInvariant
TerminationProp == <> (pc = "Done")
FinalStateProps == (pc = "Done") => (PermInvariant /\ SortedInvariant)

============================================================================
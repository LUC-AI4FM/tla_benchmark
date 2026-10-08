---- MODULE RecursiveMergesort ----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES arr, b, stack, pc, i, j, k, left, right, mid, temp

Init == 
  /\ arr \in [1..ArrayLen -> Nat]
  /\ b \in [1..ArrayLen -> Nat]
  /\ stack = << >>
  /\ pc = "Start"
  /\ i = 0
  /\ j = 0
  /\ k = 0
  /\ left = 0
  /\ right = 0
  /\ mid = 0

Next ==
  \/ \E x \in {"Start", "Push", "MergeSort1", "MergeSort2", "If1", "If2", "Merge"} :
      /\ pc = x
      /\ \/ x = "Start" -> ['][pc' = "Push"]
         \/ x = "Push" -> ['][stack' = <<left, right>> \o stack; pc' = "MergeSort1"; left' = 1; right' = ArrayLen]
         \/ x = "MergeSort1" -> ['][IF left < right THEN mid' = (left + right) \div 2; pc' = "If1"]
         \/ x = "MergeSort2" -> ['][IF ~ (left < right) THEN pc' = "Pop"]]
         \/ x = "If1" -> ['][stack' = <<mid+1, right>> \o stack; pc' = "Push"; left' = left; right' = mid]
         \/ x = "If2" -> ['][pc' = "MergeSort2"]
         \/ x = "Merge" -> ['][pc' = "Pop"]]
  \/ /\ pc = "Pop"
     /\ \E l, r \in Nat :
        /\ stack # << >>
        /\ LET top == Head(stack)
           tail == Tail(stack) IN
        /\ ['][stack' = tail; left' = Head(top); right' = Second(top); mid' = (left + right) \div 2; pc' = "If2"; i' = left'; j' = mid'+1; k' = left']
     /\ \/ (i <= mid) /\ (j <= right) -> ['][IF arr[i] <= arr[j] THEN b[k'] = arr[i]; i' = i+1 ELSE b[k'] = arr[j]; j' = j+1]; pc' = "Merge"]
        \/ (i > mid) /\ (j <= right) -> ['][b[k'] = arr[j]; j' = j+1; pc' = "Merge"]]
        \/ (i <= mid) /\ (j > right) -> ['][b[k'] = arr[i]; i' = i+1; pc' = "Merge"]]
        \/ (i > mid) /\ (j > right) -> ['][pc' = "Copy"]
  \/ /\ pc = "Copy"
     /\ k <= right
     /\ ['][arr[k] = b[k]; k' = k+1]
     /\ IF k+1 > right THEN ['][pc' = "Pop"] ELSE ['][pc' = "Copy"]

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, i, j, k, left, mid, right>>
  /\ <><pc = "Done">>_<<pc, stack, i, j, k, left, mid, right>>

DoneSort ==
  /\ pc = "Done"
  /\ \A x, y \in 1..ArrayLen : x <= y => arr[x] <= arr[y]

THEOREM Spec => []DoneSort

====
------------------------------- MODULE MergeSortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES a, b, stack, pc, i, j, k, m, l, r, N

Init == 
  /\ N \in 0..ArrayLen
  /\ a \in [1..N -> 1..N]
  /\ b = << >>
  /\ stack = << >>
  /\ pc = "Start"
  /\ i = 0
  /\ j = 0
  /\ k = 0
  /\ m = 0
  /\ l = 0
  /\ r = 0

Next ==
  \/ /\ pc = "Start"
     /\ N > 0
     /\ stack' = <<[l |-> 1, r |-> N]>>
     /\ pc' = "Sort"
  \/ /\ pc = "Start"
     /\ N = 0
     /\ pc' = "Done"
  \/ /\ pc = "Sort"
     /\ LET top == Head(stack)
          l == top[l]
          r == top[r]
      IN
        \/ /\ l < r
           /\ m' = (l + r) \div 2
           /\ stack' = Append(Append(Tail(stack), <<[l |-> l, r |-> m']>>), <<[l |-> m'+1, r |-> r]>>)
           /\ pc' = "Sort"
        \/ /\ l >= r
           /\ stack' = Tail(stack)
           /\ pc' = IF stack = << >> THEN "Done" ELSE "Merge"
  \/ /\ pc = "Merge"
     /\ LET top == Head(stack)
          l == top[l]
          r == top[r]
          m == (l + r) \div 2
      IN
        /\ i' = l
        /\ j' = m+1
        /\ k' = l
        /\ pc' = "CopyLeft"
  \/ /\ pc = "CopyLeft"
     /\ i <= m
     /\ b' = Append(b, a[i])
     /\ i' = i + 1
     /\ pc' = "CopyLeft"
  \/ /\ pc = "CopyLeft"
     /\ i > m
     /\ j' = r
     /\ pc' = "CopyRight"
  \/ /\ pc = "CopyRight"
     /\ j >= m+1
     /\ b' = Append(b, a[j])
     /\ j' = j - 1
     /\ pc' = "CopyRight"
  \/ /\ pc = "CopyRight"
     /\ j < m+1
     /\ k' = l
     /\ pc' = "MergeLoop"
  \/ /\ pc = "MergeLoop"
     /\ k <= r
     /\ (i > m
         -> /\ a'[k] = b[j]
            /\ j' = j + 1)
     /\ (j > r
         -> /\ a'[k] = b[i]
            /\ i' = i + 1)
     /\ (i <= m /\ j <= r
         -> /\ a'[k] = IF b[i] <= b[j] THEN b[i] ELSE b[j]
            /\ IF b[i] <= b[j] THEN i' = i + 1 ELSE j' = j + 1)
     /\ k' = k + 1
     /\ pc' = "MergeLoop"
  \/ /\ pc = "MergeLoop"
     /\ k > r
     /\ stack' = Tail(stack)
     /\ pc' = IF stack = << >> THEN "Done" ELSE "Merge"

Spec ==
  /\ Init
  /\ [][Next]_<<a, b, stack, pc, i, j, k, m, l, r>>
  /\ WF_next(<<a, b, stack, pc, i, j, k, m, l, r>>)

Invariant ==
  \/ pc = "Done"
     /\ \A x \in DOMAIN a : \A y \in DOMAIN a : (x <= y) => a[x] <= a[y]

Termination ==
  <>[](pc = "Done")

PossibleCounts ==
  /\ TLCGet("states") = 12
  /\ TLCGet("mergeSteps") = 8

=============================================================================
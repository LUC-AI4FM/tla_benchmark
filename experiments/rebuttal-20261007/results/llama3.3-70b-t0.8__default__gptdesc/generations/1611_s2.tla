```
MODULE Mergesort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen, N
VARIABLES pc, array, b, callStack

Init ==
  /\ pc = "Start"
  /\ array \in [1..N -> 1..N]
  /\ b = <<>>
  /\ callStack = <<>>

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "Sort"
    /\ array' = array
    /\ b' = b
    /\ callStack' = <<["start", 1, ArrayLen]>>
  /\ (pc = "Sort") =>
    /\ IF (callStack # <<>>) THEN
        /\ LET idx == Head(Head(callStack)) IN
        /\ LET l == Head(Tail(Head(callStack))) IN
        /\ LET r == Tail(Tail(Head(callStack))) IN
        /\ IF (l = r) THEN
            /\ pc' = "Done"
            /\ array' = array
            /\ b' = b
            /\ callStack' = Tail(callStack)
          ELSE
            /\ LET m == (l + r) \div 2 IN
            /\ pc' = "Sort"
            /\ array' = array
            /\ b' = b
            /\ callStack' = <<["sort", idx, l, m], ["sort", idx, m+1, r]>> @@ Tail(callStack)
        /\ ELSE
            /\ pc' = "Done"
            /\ array' = array
            /\ b' = b
            /\ callStack' = callStack
  /\ (pc = "Merge") =>
    /\ IF (callStack # <<>>) THEN
        /\ LET idx == Head(Head(callStack)) IN
        /\ LET l == Head(Tail(Head(callStack))) IN
        /\ LET r == Tail(Tail(Head(callStack))) IN
        /\ pc' = "Done"
        /\ array' = Merge(array, b, l, r)
        /\ b' = <<>>
        /\ callStack' = Tail(callStack)
      /\ ELSE
          /\ pc' = pc
          /\ array' = array
          /\ b' = b
          /\ callStack' = callStack

Spec ==
  /\ Init
  /\ [][Next]_<<pc, array, b, callStack>>
  /\ WF_<<pc, array, b, callStack>>(Next)

THEOREM Spec => []pc = "Done" ~> Sorted(array)
Sorted(a) == a[1] <= a[2] ∧ ... ∧ a[N-1] <= a[N]

Merge(a, b, l, r) ==
  IF (l > r) THEN
    <<>>
  ELSE
    IF (a[l] <= a[r]) THEN
      Concat(<<a[l]>>, Merge(Tail(a), b, l+1, r))
    ELSE
      Concat(<<a[r]>>, Merge(a, Tail(b), l, r-1))

SANY_parity == 
  /\ pc \in {"Start", "Sort", "Merge", "Done"}
  /\ array \in [1..N -> 1..N]
  /\ b \in Seq(1..N)
  /\ callStack \in Seq([["start" | "sort", Int, Int, Int]])
```
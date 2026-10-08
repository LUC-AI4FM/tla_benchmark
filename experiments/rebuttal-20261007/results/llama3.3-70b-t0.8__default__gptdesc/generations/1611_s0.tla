```
MODULE Mergesort
EXTENDS Integers, Sequences, TLC

CONSTANTS ArrayLen, N

VARIABLES pc, array, b, stack

Init ==
  /\ pc = "Start"
  /\ array \in [1..ArrayLen -> 1..N]
  /\ b = <<>>
  /\ stack = <<>>

Next ==
  /\ pc = "Start" =>
    /\ pc' = "Sort"
    /\ array' = array
    /\ b' = <<>>
    /\ stack' = <<["array", 1, ArrayLen]>>
  \/ pc = "Sort" =>
    (\* non-terminal case: split and recurse *\) 
    /\ \exists l, r \in 1..ArrayLen :
      /\ [l, r] = Head(stack)
      /\ l < r
      /\ mid == (l + r) \div 2
      /\ pc' = "Sort"
      /\ array' = array
      /\ b' = <<>>
      /\ stack' = Append(Tail(stack), <<[l, mid]>>, <<[mid+1, r]>>)
    \/ (\* terminal case: copy and merge *\) 
       \exists l, r \in 1..ArrayLen :
         /\ [l, r] = Head(stack)
         /\ l = r
         /\ pc' = "Copy"
         /\ array' = array
         /\ b' = <<>>
         /\ stack' = Tail(stack)
  \/ pc = "Copy" =>
    (\* copy elements to buffer *\) 
    /\ \exists l, r \in 1..ArrayLen :
      /\ [l, r] = Head(stack)
      /\ b' = Append(b, <<array[l]>>)
      /\ pc' = IF r = l THEN "Merge" ELSE "Copy"
      /\ array' = array
      /\ stack' = IF r = l THEN Tail(stack) ELSE <<[l+1, r]>>
  \/ pc = "Merge" =>
    (\* merge adjacent sorted segments *\) 
    /\ \exists l, m, r \in 1..ArrayLen :
      /\ [l, r] = Head(stack)
      /\ m = (l + r) \div 2
      /\ b' = Merge(b, array, l, m, r)
      /\ pc' = IF Tail(stack) = <<>> THEN "Done" ELSE "Sort"
      /\ array' = IF Tail(stack) = <<>> THEN b ELSE array
      /\ stack' = Tail(stack)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, array, b, stack>>
  /\ WF_<<pc, array, b, stack>>(Next)

THEOREM Spec => []pc = "Done" => Sorted(array)

Sorted(s) == \A i, j \in Domain s : i <= j => s[i] <= s[j]

Merge(b, a, l, m, r) ==
  IF b = <<>> THEN
    <<>>
  ELSE
    LET left == Take(m - l + 1, Drop(l-1, a))
        right == Take(r - m, Drop(m, a)) IN
      MergeStep(b, left, right)

MergeStep(b, left, right) ==
  IF left = <<>> THEN
    Append(b, right)
  ELSE IF right = <<>> THEN
    Append(b, left)
  ELSE
    LET lh == Head(left)
        rh == Head(right) IN
      IF lh <= rh THEN
        Append(MergeStep(Tail(b), Tail(left), right), <<lh>>)
      ELSE
        Append(MergeStep(Tail(b), left, Tail(right)), <<rh>>)

```
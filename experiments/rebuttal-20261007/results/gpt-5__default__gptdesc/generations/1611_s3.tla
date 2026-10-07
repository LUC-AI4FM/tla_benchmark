---- MODULE MergeSort ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, ArrayLen

VARIABLES a, b, stack, pc

vars == << a, b, stack, pc >>

Mid(l, r) == l + ((r - l) \div 2)

Top(s) == s[Len(s)]

Pop(s) == SubSeq(s, 1, Len(s) - 1)

Push3(s, x, y, z) == Append(Append(Append(s, x), y), z)

ReplaceTop(s, new) == [s EXCEPT ![Len(s)] = new]

SortFrame(l, r) ==
  [ type |-> "Sort",
    l |-> l,
    r |-> r ]

MergeFrame(l, m, r) ==
  [ type |-> "Merge",
    l |-> l,
    m |-> m,
    r |-> r,
    i |-> l,
    j |-> m + 1,
    k |-> l,
    phase |-> "merge" ]

IsNondecreasing(s) ==
  \A i \in 1..(Max(0, Len(s) - 1)) : s[i] <= s[i + 1]

Init ==
  /\ a \in Seq(1..N)
  /\ Len(a) <= ArrayLen
  /\ b = a
  /\ IF Len(a) <= 1
        THEN /\ stack = << >>
             /\ pc = "Done"
        ELSE /\ stack = << SortFrame(1, Len(a)) >>
             /\ pc = "Run"

DoSort ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Sort"
  /\ LET f == Top(stack) IN
     LET l == f.l IN
     LET r == f.r IN
     IF l >= r THEN
       LET ns == Pop(stack) IN
         /\ stack' = ns
         /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
         /\ UNCHANGED << a, b >>
     ELSE
       LET m == Mid(l, r) IN
       LET ns == Push3(Pop(stack),
                       MergeFrame(l, m, r),
                       SortFrame(m + 1, r),
                       SortFrame(l, m)) IN
         /\ stack' = ns
         /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
         /\ UNCHANGED << a, b >>

MergeTakeLeft ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET l == f.l IN
     LET m == f.m IN
     LET r == f.r IN
     LET i == f.i IN
     LET j == f.j IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "merge"
     /\ i <= m /\ j <= r /\ a[i] <= a[j]
     /\ LET newTop == [f EXCEPT !.i = i + 1, !.k = k + 1] IN
        LET nb == [b EXCEPT ![k] = a[i]] IN
        LET ns == ReplaceTop(stack, newTop) IN
          /\ b' = nb
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED a

MergeTakeRight ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET l == f.l IN
     LET m == f.m IN
     LET r == f.r IN
     LET i == f.i IN
     LET j == f.j IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "merge"
     /\ i <= m /\ j <= r /\ a[i] > a[j]
     /\ LET newTop == [f EXCEPT !.j = j + 1, !.k = k + 1] IN
        LET nb == [b EXCEPT ![k] = a[j]] IN
        LET ns == ReplaceTop(stack, newTop) IN
          /\ b' = nb
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED a

DrainLeft ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET l == f.l IN
     LET m == f.m IN
     LET r == f.r IN
     LET i == f.i IN
     LET j == f.j IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "merge"
     /\ i <= m /\ j > r
     /\ LET newTop == [f EXCEPT !.i = i + 1, !.k = k + 1] IN
        LET nb == [b EXCEPT ![k] = a[i]] IN
        LET ns == ReplaceTop(stack, newTop) IN
          /\ b' = nb
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED a

DrainRight ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET l == f.l IN
     LET m == f.m IN
     LET r == f.r IN
     LET i == f.i IN
     LET j == f.j IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "merge"
     /\ j <= r /\ i > m
     /\ LET newTop == [f EXCEPT !.j = j + 1, !.k = k + 1] IN
        LET nb == [b EXCEPT ![k] = a[j]] IN
        LET ns == ReplaceTop(stack, newTop) IN
          /\ b' = nb
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED a

BeginCopyBack ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET l == f.l IN
     LET m == f.m IN
     LET r == f.r IN
     LET i == f.i IN
     LET j == f.j IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "merge"
     /\ i > m /\ j > r
     /\ LET newTop == [f EXCEPT !.phase = "copyBack", !.k = l] IN
        LET ns == ReplaceTop(stack, newTop) IN
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED << a, b >>

CopyBack ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET r == f.r IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "copyBack"
     /\ k <= r
     /\ LET newTop == [f EXCEPT !.k = k + 1] IN
        LET na == [a EXCEPT ![k] = b[k]] IN
        LET ns == ReplaceTop(stack, newTop) IN
          /\ a' = na
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED b

FinishMerge ==
  /\ Len(stack) > 0
  /\ Top(stack).type = "Merge"
  /\ LET f == Top(stack) IN
     LET r == f.r IN
     LET k == f.k IN
     LET phase == f.phase IN
     /\ phase = "copyBack"
     /\ k > r
     /\ LET ns == Pop(stack) IN
          /\ stack' = ns
          /\ pc' = IF Len(ns) = 0 THEN "Done" ELSE "Run"
          /\ UNCHANGED << a, b >>

Next ==
  DoSort
  \/ MergeTakeLeft
  \/ MergeTakeRight
  \/ DrainLeft
  \/ DrainRight
  \/ BeginCopyBack
  \/ CopyBack
  \/ FinishMerge

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

SortedWhenDone == (pc = "Done") => IsNondecreasing(a)

Termination == <> (pc = "Done")
====
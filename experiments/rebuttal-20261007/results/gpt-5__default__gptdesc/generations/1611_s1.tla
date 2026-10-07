------------------------------ MODULE MergeSortRec ------------------------------

EXTENDS Naturals, Integers, Sequences

CONSTANTS N, ArrayLen

VARIABLES a, b, L, stack, pc

(*
  Helpers for the explicit call stack
*)
Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s)-1)
Push(s, e) == Append(s, e)
ReplaceTop(s, e) == Append(SubSeq(s, 1, Len(s)-1), e)

Mid(l, r) == (l + r) \div 2

SortType == [type: {"Sort"}, l: Nat, r: Nat, stage: {"start", "afterLeft", "afterRight", "afterMerge"}]
MergeType == [type: {"Merge"}, l: Nat, m: Nat, r: Nat, i: Nat, j: Nat, k: Nat, phase: {"merge", "copy"}]
FrameType == SortType \cup MergeType

Indices == 1..L

Sorted(arr, len) ==
  \A i, j \in 1..len : i < j => arr[i] <= arr[j]

TypeInv ==
  /\ L \in 0..ArrayLen
  /\ a \in [1..L -> 1..N]
  /\ b \in [1..L -> 1..N]
  /\ pc \in {"Run", "Done"}
  /\ stack \in Seq(FrameType)

Init ==
  /\ L \in 0..ArrayLen
  /\ a \in [1..L -> 1..N]
  /\ b \in [1..L -> 1..N]
  /\ pc = "Run"
  /\ stack =
       IF L <= 1
         THEN << >>
         ELSE << [type |-> "Sort", l |-> 1, r |-> L, stage |-> "start"] >>

(*
  Actions implementing the mergesort with an explicit stack.
*)

SortStart ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
       /\ f.type = "Sort"
       /\ f.stage = "start"
       /\ IF f.l >= f.r
            THEN /\ stack' = Pop(stack)
                 /\ UNCHANGED << a, b, L, pc >>
            ELSE LET m == Mid(f.l, f.r) IN
                 /\ stack' =
                      Push( ReplaceTop(stack, [type |-> "Sort", l |-> f.l, r |-> f.r, stage |-> "afterLeft"]),
                            [type |-> "Sort", l |-> f.l, r |-> m, stage |-> "start"] )
                 /\ UNCHANGED << a, b, L, pc >>

SortAfterLeft ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
       /\ f.type = "Sort"
       /\ f.stage = "afterLeft"
       /\ LET l == f.l IN LET r == f.r IN LET m == Mid(l, r) IN
          /\ stack' =
               Push( ReplaceTop(stack, [type |-> "Sort", l |-> l, r |-> r, stage |-> "afterRight"]),
                     [type |-> "Sort", l |-> m+1, r |-> r, stage |-> "start"] )
          /\ UNCHANGED << a, b, L, pc >>

SortAfterRight ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
       /\ f.type = "Sort"
       /\ f.stage = "afterRight"
       /\ LET l == f.l IN LET r == f.r IN LET m == Mid(l, r) IN
          /\ stack' =
               Push( ReplaceTop(stack, [type |-> "Sort", l |-> l, r |-> r, stage |-> "afterMerge"]),
                     [type |-> "Merge", l |-> l, m |-> m, r |-> r, i |-> l, j |-> m+1, k |-> l, phase |-> "merge"] )
          /\ UNCHANGED << a, b, L, pc >>

SortAfterMerge ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
       /\ f.type = "Sort"
       /\ f.stage = "afterMerge"
       /\ stack' = Pop(stack)
       /\ UNCHANGED << a, b, L, pc >>

MergeTakeLeft ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
     LET l == f.l IN LET m == f.m IN LET r == f.r IN
     LET i == f.i IN LET j == f.j IN LET k == f.k IN
       /\ f.type = "Merge"
       /\ f.phase = "merge"
       /\ i <= m
       /\ (j > r \/ a[i] <= a[j])
       /\ b' = [b EXCEPT ![k] = a[i]]
       /\ LET newK == k + 1 IN
          LET newPhase == IF newK <= r THEN "merge" ELSE "copy" IN
          LET newK2 == IF newPhase = "merge" THEN newK ELSE l IN
          LET f2 == [f EXCEPT !.i = i+1, !.k = newK2, !.phase = newPhase] IN
             /\ stack' = ReplaceTop(stack, f2)
       /\ UNCHANGED << a, L, pc >>

MergeTakeRight ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
     LET l == f.l IN LET m == f.m IN LET r == f.r IN
     LET i == f.i IN LET j == f.j IN LET k == f.k IN
       /\ f.type = "Merge"
       /\ f.phase = "merge"
       /\ j <= r
       /\ (i > m \/ a[i] > a[j])
       /\ b' = [b EXCEPT ![k] = a[j]]
       /\ LET newK == k + 1 IN
          LET newPhase == IF newK <= r THEN "merge" ELSE "copy" IN
          LET newK2 == IF newPhase = "merge" THEN newK ELSE l IN
          LET f2 == [f EXCEPT !.j = j+1, !.k = newK2, !.phase = newPhase] IN
             /\ stack' = ReplaceTop(stack, f2)
       /\ UNCHANGED << a, L, pc >>

MergeCopy ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET f == Top(stack) IN
     LET l == f.l IN LET r == f.r IN LET k == f.k IN
       /\ f.type = "Merge"
       /\ f.phase = "copy"
       /\ a' = [a EXCEPT ![k] = b[k]]
       /\ LET newK == k + 1 IN
            IF newK <= r
              THEN /\ stack' = [stack EXCEPT ![Len(stack)] = [f EXCEPT !.k = newK]]
              ELSE /\ stack' = Pop(stack)
       /\ UNCHANGED << b, L, pc >>

BaseDone ==
  /\ pc = "Run"
  /\ (L <= 1 \/ Len(stack) = 0)
  /\ pc' = "Done"
  /\ UNCHANGED << a, b, L, stack >>

Next ==
  SortStart
  \/ SortAfterLeft
  \/ SortAfterRight
  \/ SortAfterMerge
  \/ MergeTakeLeft
  \/ MergeTakeRight
  \/ MergeCopy
  \/ BaseDone

vars == << a, b, L, stack, pc >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

DoneSorted == [](pc = "Done" => Sorted(a, L))

Termination == <> (pc = "Done")

=============================================================================
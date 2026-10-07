----------------------------- MODULE MergeSort -----------------------------
EXTENDS Naturals, Integers, Sequences

CONSTANTS N, ArrayLen

VARIABLES a, b, len, stack, pc

vars == << a, b, len, stack, pc >>

Domain == 1..len
Val == 1..N

FramesBase ==
  IF len = 0 THEN {}
  ELSE [ l: 1..len,
         r: 1..len,
         m: 0..len,
         phase: {"split","afterLeft","afterRight","merge","copy"},
         i: 0..(len+1),
         j: 0..(len+1),
         k: 0..(len+1) ]

Frames ==
  IF len = 0 THEN {}
  ELSE { f \in FramesBase : f.l <= f.r }

Top(s) == Head(s)
Push(s, f) == << f >> \o s
Pop(s) == Tail(s)
ReplaceTop(s, f) == << f >> \o Tail(s)

NewFrame(l, r) ==
  [ l |-> l, r |-> r, m |-> 0, phase |-> "split", i |-> 0, j |-> 0, k |-> 0 ]

TypeOK ==
  /\ len \in 0..ArrayLen
  /\ a \in [Domain -> Val]
  /\ b \in [Domain -> Val]
  /\ pc \in {"Start","Run","Done"}
  /\ stack \in Seq(Frames)

IsSorted(A, L) ==
  IF L <= 1 THEN TRUE ELSE \A i \in 1..(L - 1) : A[i] <= A[i + 1]

SortedAtDone == (pc = "Done") => IsSorted(a, len)

Init ==
  /\ len \in 0..ArrayLen
  /\ LET D == 1..len IN
       /\ a \in [D -> 1..N]
       /\ b \in [D -> 1..N]
  /\ pc = "Start"
  /\ stack = IF len = 0 THEN << >> ELSE << NewFrame(1, len) >>

StartStep ==
  /\ pc = "Start"
  /\ pc' = "Run"
  /\ UNCHANGED << a, b, len, stack >>

SplitStep ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "split"
       /\ IF f.l >= f.r
             THEN stack' = Pop(stack)
             ELSE
               LET m == (f.l + f.r) \div 2
                   f1 == [f EXCEPT !.m = m, !.phase = "afterLeft"]
                   left == NewFrame(f.l, m)
               IN stack' = Push(ReplaceTop(stack, f1), left)
  /\ UNCHANGED << a, b, len, pc >>

AfterLeftStep ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "afterLeft"
       /\ LET right == NewFrame(f.m + 1, f.r)
          IN stack' = Push(ReplaceTop(stack, [f EXCEPT !.phase = "afterRight"]), right)
  /\ UNCHANGED << a, b, len, pc >>

AfterRightStep ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "afterRight"
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.phase = "merge",
                                              !.i = f.l,
                                              !.j = f.m + 1,
                                              !.k = f.l])
  /\ UNCHANGED << a, b, len, pc >>

MergeTakeLeft ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "merge"
       /\ f.k <= f.r
       /\ f.i <= f.m
       /\ f.j <= f.r
       /\ a[f.i] <= a[f.j]
       /\ b' = [b EXCEPT ![f.k] = a[f.i]]
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.i = f.i + 1, !.k = f.k + 1])
  /\ UNCHANGED << a, len, pc >>

MergeTakeRight ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "merge"
       /\ f.k <= f.r
       /\ f.i <= f.m
       /\ f.j <= f.r
       /\ a[f.i] > a[f.j]
       /\ b' = [b EXCEPT ![f.k] = a[f.j]]
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.j = f.j + 1, !.k = f.k + 1])
  /\ UNCHANGED << a, len, pc >>

MergeCopyLeftRemainder ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "merge"
       /\ f.k <= f.r
       /\ f.i <= f.m
       /\ f.j > f.r
       /\ b' = [b EXCEPT ![f.k] = a[f.i]]
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.i = f.i + 1, !.k = f.k + 1])
  /\ UNCHANGED << a, len, pc >>

MergeCopyRightRemainder ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "merge"
       /\ f.k <= f.r
       /\ f.i > f.m
       /\ f.j <= f.r
       /\ b' = [b EXCEPT ![f.k] = a[f.j]]
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.j = f.j + 1, !.k = f.k + 1])
  /\ UNCHANGED << a, len, pc >>

MergeDoneToCopy ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "merge"
       /\ f.k > f.r
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.phase = "copy", !.k = f.l])
  /\ UNCHANGED << a, b, len, pc >>

CopyWriteStep ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "copy"
       /\ f.k <= f.r
       /\ a' = [a EXCEPT ![f.k] = b[f.k]]
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.k = f.k + 1])
  /\ UNCHANGED << b, len, pc >>

CopyPopStep ==
  /\ pc # "Done"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.phase = "copy"
       /\ f.k > f.r
       /\ stack' = Pop(stack)
  /\ UNCHANGED << a, b, len, pc >>

DoneWhenEmpty ==
  /\ pc # "Done" = FALSE
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << a, b, len, stack >>

Next ==
  StartStep
  \/ SplitStep
  \/ AfterLeftStep
  \/ AfterRightStep
  \/ MergeTakeLeft
  \/ MergeTakeRight
  \/ MergeCopyLeftRemainder
  \/ MergeCopyRightRemainder
  \/ MergeDoneToCopy
  \/ CopyWriteStep
  \/ CopyPopStep
  \/ DoneWhenEmpty

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")
===========================================================================
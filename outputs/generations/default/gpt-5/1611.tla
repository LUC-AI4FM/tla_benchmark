----------------------------- MODULE RecursiveMergeSort -----------------------------
EXTENDS Naturals, Integers, Sequences

CONSTANTS N, ArrayLen

VARIABLES a, b, len, stack, pc

Phase == {"call","left","afterLeft","afterRight","merge","copy","ret"}

FrameSet(len) ==
  [ lo   : 1..(len+1),
    hi   : 1..(len+1),
    mid  : 1..(len+1),
    i    : 1..(len+1),
    j    : 1..(len+1),
    k    : 1..(len+1),
    phase: Phase ]

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)
ReplaceTop(s, x) == Append(Pop(s), x)

TypeOK ==
  /\ len \in 0..ArrayLen
  /\ a \in [1..len -> 1..N]
  /\ b \in [1..len -> 1..N]
  /\ stack \in Seq(FrameSet(len))
  /\ pc \in {"Run","Done"}
  /\ \A idx \in 1..Len(stack) :
        LET f == stack[idx] IN
          /\ f.lo <= f.hi
          /\ f.lo <= f.mid
          /\ f.mid <= f.hi

IsSorted(A, n) ==
  \A i, j \in 1..n : (i < j) => A[i] <= A[j]

SortedWhenDone ==
  (pc = "Done") => IsSorted(a, len)

Init ==
  /\ len \in 0..ArrayLen
  /\ a \in [1..len -> 1..N]
  /\ b \in [1..len -> 1..N]
  /\ stack = << [lo |-> 1, hi |-> len+1, mid |-> 1, i |-> 1, j |-> 1, k |-> 1, phase |-> "call"] >>
  /\ pc = "Run"

Finish ==
  /\ pc = "Run"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << a, b, len, stack >>

CallBase ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "call"
        /\ fr.hi - fr.lo <= 1
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.phase = "ret"])
  /\ UNCHANGED << a, b, len, pc >>

CallSplit ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "call"
        /\ fr.hi - fr.lo > 1
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.phase = "left", !.mid = (fr.lo + fr.hi) \div 2])
  /\ UNCHANGED << a, b, len, pc >>

LeftPush ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "left"
        /\ stack' =
             Append(
               ReplaceTop(stack, [fr EXCEPT !.phase = "afterLeft"]),
               [lo |-> fr.lo, hi |-> fr.mid, mid |-> fr.lo,
                i |-> fr.lo, j |-> fr.lo, k |-> fr.lo,
                phase |-> "call"])
  /\ UNCHANGED << a, b, len, pc >>

RightPush ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "afterLeft"
        /\ stack' =
             Append(
               ReplaceTop(stack, [fr EXCEPT !.phase = "afterRight"]),
               [lo |-> fr.mid, hi |-> fr.hi, mid |-> fr.mid,
                i |-> fr.mid, j |-> fr.mid, k |-> fr.mid,
                phase |-> "call"])
  /\ UNCHANGED << a, b, len, pc >>

PrepareMerge ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "afterRight"
        /\ stack' = ReplaceTop(stack,
                               [fr EXCEPT !.phase = "merge",
                                            !.i = fr.lo, !.j = fr.mid, !.k = fr.lo])
  /\ UNCHANGED << a, b, len, pc >>

MergeLeft ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "merge"
        /\ fr.i < fr.mid
        /\ (fr.j = fr.hi \/ a[fr.i] <= a[fr.j])
        /\ a' = a
        /\ b' = [b EXCEPT ![fr.k] = a[fr.i]]
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.i = fr.i + 1, !.k = fr.k + 1])
  /\ UNCHANGED << len, pc >>

MergeRight ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "merge"
        /\ fr.j < fr.hi
        /\ (fr.i = fr.mid \/ a[fr.j] < a[fr.i])
        /\ a' = a
        /\ b' = [b EXCEPT ![fr.k] = a[fr.j]]
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.j = fr.j + 1, !.k = fr.k + 1])
  /\ UNCHANGED << len, pc >>

MergeDone ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "merge"
        /\ fr.i = fr.mid /\ fr.j = fr.hi
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.phase = "copy", !.i = fr.lo])
  /\ UNCHANGED << a, b, len, pc >>

CopyStep ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "copy"
        /\ fr.i < fr.hi
        /\ a' = [a EXCEPT ![fr.i] = b[fr.i]]
        /\ b' = b
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.i = fr.i + 1])
  /\ UNCHANGED << len, pc >>

CopyDone ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "copy"
        /\ fr.i = fr.hi
        /\ stack' = ReplaceTop(stack, [fr EXCEPT !.phase = "ret"])
  /\ UNCHANGED << a, b, len, pc >>

Return ==
  /\ pc = "Run"
  /\ Len(stack) >= 1
  /\ LET fr == Top(stack) IN
        /\ fr.phase = "ret"
        /\ stack' = Pop(stack)
  /\ UNCHANGED << a, b, len, pc >>

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED << a, b, len, stack, pc >>

Next ==
  Finish
  \/ CallBase
  \/ CallSplit
  \/ LeftPush
  \/ RightPush
  \/ PrepareMerge
  \/ MergeLeft
  \/ MergeRight
  \/ MergeDone
  \/ CopyStep
  \/ CopyDone
  \/ Return
  \/ DoneStutter

vars == << a, b, len, stack, pc >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

=============================================================================
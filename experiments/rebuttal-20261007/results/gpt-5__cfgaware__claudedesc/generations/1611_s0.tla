---- MODULE MergeSortPlusCal ----
EXTENDS Naturals, Sequences, TLC

CONSTANT ArrayLen
CONSTANT defaultInitValue

VARIABLES pc, n, a, b, stack, mergeCount, finishCount

Phases == {"split", "leftPending", "rightPending", "copyL", "copyR", "merge", "return"}

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)
Push(s, x) == Append(s, x)
UpdateTop(s, x) == [s EXCEPT ![Len(s)] = x]

Mid(l, r) == (l + r) \div 2

IsSorted(A, N) ==
  \A i, j \in 1..N : i <= j => A[i] <= A[j]

Init ==
  /\ pc = "Init"
  /\ n \in 0..ArrayLen
  /\ a \in [1..n -> 1..n]
  /\ b \in [1..n -> 1..n]
  /\ stack = << >>
  /\ mergeCount = 0
  /\ finishCount = 0

Start ==
  /\ pc = "Init"
  /\ IF n <= 1
        THEN /\ pc' = "Done"
             /\ finishCount' = finishCount + 1
             /\ UNCHANGED << a, b, n, stack, mergeCount >>
        ELSE /\ pc' = "Step"
             /\ stack' = << [l |-> 1, r |-> n, m |-> 0, phase |-> "split",
                              i |-> 0, j |-> 0, k |-> 0, t |-> 0] >>
             /\ UNCHANGED << a, b, n, mergeCount, finishCount >>

StepEmpty ==
  /\ pc = "Step"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ finishCount' = finishCount + 1
  /\ UNCHANGED << a, b, n, stack, mergeCount >>

BaseCase ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN fr.r <= fr.l
  /\ stack' = Pop(stack)
  /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

SplitAction ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.r > fr.l
       /\ fr.phase = "split"
       /\ LET m == Mid(fr.l, fr.r) IN
            /\ stack' =
               Push(
                 UpdateTop(stack, [fr EXCEPT !.m = m, !.phase = "leftPending"]),
                 [l |-> fr.l, r |-> m, m |-> 0, phase |-> "split",
                  i |-> 0, j |-> 0, k |-> 0, t |-> 0]
               )
  /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

RightPush ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.r > fr.l
       /\ fr.phase = "leftPending"
       /\ stack' =
            Push(
              UpdateTop(stack, [fr EXCEPT !.phase = "rightPending"]),
              [l |-> fr.m + 1, r |-> fr.r, m |-> 0, phase |-> "split",
               i |-> 0, j |-> 0, k |-> 0, t |-> 0]
            )
  /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

GotoCopyL ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.r > fr.l
       /\ fr.phase = "rightPending"
       /\ stack' = UpdateTop(stack, [fr EXCEPT !.phase = "copyL", !.t = fr.l])
  /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

CopyLeftStep ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.r > fr.l
       /\ fr.phase = "copyL"
       /\ IF fr.t <= fr.m
            THEN /\ b' = [b EXCEPT ![fr.t] = a[fr.t]]
                 /\ stack' = UpdateTop(stack, [fr EXCEPT !.t = fr.t + 1])
                 /\ UNCHANGED << a, n, pc, mergeCount, finishCount >>
            ELSE /\ stack' = UpdateTop(stack, [fr EXCEPT !.phase = "copyR", !.t = fr.m + 1, !.j = fr.r])
                 /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

CopyRightStep ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.r > fr.l
       /\ fr.phase = "copyR"
       /\ IF fr.t <= fr.r
            THEN /\ b' = [b EXCEPT ![fr.j] = a[fr.t]]
                 /\ stack' = UpdateTop(stack, [fr EXCEPT !.j = fr.j - 1, !.t = fr.t + 1])
                 /\ UNCHANGED << a, n, pc, mergeCount, finishCount >>
            ELSE /\ stack' = UpdateTop(stack, [fr EXCEPT !.phase = "merge", !.i = fr.l, !.j = fr.r, !.k = fr.l])
                 /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

MergeStep ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.r > fr.l
       /\ fr.phase = "merge"
       /\ IF fr.k <= fr.r
            THEN
              /\ IF fr.i <= fr.m /\ (fr.j < fr.m + 1 \/ b[fr.i] <= b[fr.j])
                   THEN /\ a' = [a EXCEPT ![fr.k] = b[fr.i]]
                        /\ stack' = UpdateTop(stack, [fr EXCEPT !.i = fr.i + 1, !.k = fr.k + 1])
                   ELSE /\ a' = [a EXCEPT ![fr.k] = b[fr.j]]
                        /\ stack' = UpdateTop(stack, [fr EXCEPT !.j = fr.j - 1, !.k = fr.k + 1])
                 /\ mergeCount' = mergeCount + 1
                 /\ UNCHANGED << b, n, pc, finishCount >>
            ELSE /\ stack' = UpdateTop(stack, [fr EXCEPT !.phase = "return"])
                 /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

ReturnStep ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN
       /\ fr.phase = "return"
       /\ stack' = Pop(stack)
  /\ UNCHANGED << a, b, n, pc, mergeCount, finishCount >>

Next ==
  Start
  \/ StepEmpty
  \/ BaseCase
  \/ SplitAction
  \/ RightPush
  \/ GotoCopyL
  \/ CopyLeftStep
  \/ CopyRightStep
  \/ MergeStep
  \/ ReturnStep

vars == << pc, n, a, b, stack, mergeCount, finishCount >>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

Invariant == pc # "Done" \/ IsSorted(a, n)

PossibleCounts == TRUE

defaultInitValue == 0
====
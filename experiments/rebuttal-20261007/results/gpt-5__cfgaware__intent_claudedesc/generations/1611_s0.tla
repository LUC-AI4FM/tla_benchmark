----------------------------- MODULE MergeSort -----------------------------
EXTENDS Naturals, Sequences

CONSTANTS
  ArrayLen,
  defaultInitValue

VARIABLES
  A,        \* array being sorted: function from 0..(N-1) to 0..N
  B,        \* temporary buffer
  Stack,    \* recursion stack of frames [l, r, st]
  M,        \* merge control record
  Done,     \* termination flag
  N         \* chosen input length in 0..ArrayLen

vars == << A, B, Stack, M, Done, N >>

Dom == 0 .. (N - 1)
Val == 0 .. N

Mid(l, r) == (l + r) \div 2

Top(s) == s[Len(s)]
Push(s, f) == Append(s, f)
Pop(s) == SubSeq(s, 1, Len(s) - 1)
SetTopSt(s, st) == [ s EXCEPT ![Len(s)].st = st ]

IsSorted(arr) ==
  LET D == DOMAIN arr IN
    \A x \in D : \A y \in D : x < y => arr[x] <= arr[y]

Init ==
  /\ N \in 0 .. ArrayLen
  /\ A \in [ Dom -> Val ]
  /\ B = [ i \in Dom |-> defaultInitValue ]
  /\ Stack =
        IF N <= 1
        THEN << >>
        ELSE << [ l |-> 0, r |-> N - 1, st |-> "init" ] >>
  /\ M = [ active |-> FALSE ]
  /\ Done = (N <= 1)

(*
 Frames on Stack are records [l, r, st] with st in {"init","afterLeft","afterRight"}.
 When a frame with st="afterRight" is on top, the next step activates a merge
 over [l..r] with m = Mid(l,r) using the mirrored buffer copy.
*)

BasePop ==
  /\ ~Done
  /\ ~M.active
  /\ Stack # << >>
  /\ LET fr == Top(Stack) IN
       /\ fr.l >= fr.r
       /\ Stack' = Pop(Stack)
  /\ UNCHANGED << A, B, M, Done, N >>

SplitLeft ==
  /\ ~Done
  /\ ~M.active
  /\ Stack # << >>
  /\ LET fr == Top(Stack) IN
     LET l == fr.l IN
     LET r == fr.r IN
     LET m == Mid(l, r) IN
       /\ fr.st = "init"
       /\ l < r
       /\ Stack' =
            Append(
              SetTopSt(Stack, "afterLeft"),
              [ l |-> l, r |-> m, st |-> "init" ]
            )
  /\ UNCHANGED << A, B, M, Done, N >>

SplitRight ==
  /\ ~Done
  /\ ~M.active
  /\ Stack # << >>
  /\ LET fr == Top(Stack) IN
     LET l == fr.l IN
     LET r == fr.r IN
     LET m == Mid(l, r) IN
       /\ fr.st = "afterLeft"
       /\ l < r
       /\ Stack' =
            Append(
              SetTopSt(Stack, "afterRight"),
              [ l |-> m + 1, r |-> r, st |-> "init" ]
            )
  /\ UNCHANGED << A, B, M, Done, N >>

ActivateMerge ==
  /\ ~Done
  /\ ~M.active
  /\ Stack # << >>
  /\ LET fr == Top(Stack) IN
     LET l == fr.l IN
     LET r == fr.r IN
     LET m == Mid(l, r) IN
       /\ fr.st = "afterRight"
       /\ l < r
       /\ M' =
            [ active |-> TRUE,
              l |-> l, r |-> r, m |-> m,
              phase |-> "copyLeft",
              i |-> m, j |-> 0, k |-> 0 ]
  /\ UNCHANGED << A, B, Stack, Done, N >>

CopyLeftStep ==
  /\ ~Done
  /\ M.active
  /\ M.phase = "copyLeft"
  /\ M.i >= M.l
  /\ B' = [ B EXCEPT ![M.i] = A[M.i] ]
  /\ M' = [ M EXCEPT !.i = @ - 1 ]
  /\ UNCHANGED << A, Stack, Done, N >>

CopyLeftToRight ==
  /\ ~Done
  /\ M.active
  /\ M.phase = "copyLeft"
  /\ M.i < M.l
  /\ M' = [ M EXCEPT !.phase = "copyRight", !.k = M.m + 1 ]
  /\ UNCHANGED << A, B, Stack, Done, N >>

CopyRightStep ==
  /\ ~Done
  /\ M.active
  /\ M.phase = "copyRight"
  /\ M.k <= M.r
  /\ B' = [ B EXCEPT ![ M.r + M.m + 1 - M.k ] = A[M.k] ]
  /\ M' = [ M EXCEPT !.k = @ + 1 ]
  /\ UNCHANGED << A, Stack, Done, N >>

CopyRightToMerge ==
  /\ ~Done
  /\ M.active
  /\ M.phase = "copyRight"
  /\ M.k > M.r
  /\ M' = [ M EXCEPT
              !.phase = "merge",
              !.i = M.l, !.j = M.r, !.k = M.l ]
  /\ UNCHANGED << A, B, Stack, Done, N >>

MergeStep ==
  /\ ~Done
  /\ M.active
  /\ M.phase = "merge"
  /\ M.k <= M.r
  /\ IF B[M.j] < B[M.i]
     THEN /\ A' = [ A EXCEPT ![M.k] = B[M.j] ]
          /\ M' = [ M EXCEPT !.j = @ - 1, !.k = @ + 1 ]
     ELSE /\ A' = [ A EXCEPT ![M.k] = B[M.i] ]
          /\ M' = [ M EXCEPT !.i = @ + 1, !.k = @ + 1 ]
  /\ UNCHANGED << B, Stack, Done, N >>

MergeDone ==
  /\ ~Done
  /\ M.active
  /\ M.phase = "merge"
  /\ M.k > M.r
  /\ Stack' = Pop(Stack)
  /\ M' = [ active |-> FALSE ]
  /\ UNCHANGED << A, B, Done, N >>

Finish ==
  /\ ~Done
  /\ ~M.active
  /\ Stack = << >>
  /\ Done' = TRUE
  /\ UNCHANGED << A, B, Stack, M, N >>

Step ==
    BasePop
  \/ SplitLeft
  \/ SplitRight
  \/ ActivateMerge
  \/ CopyLeftStep
  \/ CopyLeftToRight
  \/ CopyRightStep
  \/ CopyRightToMerge
  \/ MergeStep
  \/ MergeDone

Next == Step \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Termination == <> Done

Invariant == Done => IsSorted(A)

=============================================================================
----------------------------- MODULE MergeSort -----------------------------
EXTENDS Naturals, Sequences

CONSTANT MaxLen
ASSUME MaxLen \in Nat

VARIABLES Len, A, B, stk, pc, merges

Mid(lo, hi) == (lo + hi) \div 2

Idx == 0..(Len-1)
Val == 0..Len

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)
Push(s, e) == Append(s, e)
ReplaceTop(s, e) == [s EXCEPT ![Len(s)] = e]

FrameSet ==
  [ st : {"Recurse","LeftPending","RightPending","CopyL","CopyR","Merge"},
    lo : 0..MaxLen,
    hi : (-1)..(MaxLen-1),
    i  : (-1)..(MaxLen+1),
    j  : (-1)..(MaxLen+1),
    k  : (-1)..(MaxLen+1) ]

TypeOK ==
  /\ Len \in 0..MaxLen
  /\ A \in [Idx -> Val]
  /\ B \in [Idx -> Val]
  /\ stk \in Seq(FrameSet)
  /\ pc \in {"Run","Done"}
  /\ merges \in Nat

IsSorted(arr) ==
  \A x, y \in Idx : x < y => arr[x] <= arr[y]

Terminated == pc = "Done"

SortedWhenDone == Terminated => IsSorted(A)

Init ==
  /\ Len \in 0..MaxLen
  /\ A \in [Idx -> Val]
  /\ B \in [Idx -> Val]
  /\ merges = 0
  /\ IF Len <= 1
        THEN /\ pc = "Done"
             /\ stk = << >>
        ELSE /\ pc = "Run"
             /\ stk = << [ st |-> "Recurse",
                           lo |-> 0,
                           hi |-> Len - 1,
                           i  |-> 0,
                           j  |-> 0,
                           k  |-> 0 ] >>
  /\ TypeOK

RecurseDone ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN f.st = "Recurse" /\ f.lo >= f.hi
  /\ LET s2 == Pop(stk) IN
       /\ stk' = s2
       /\ pc' = IF Len(s2) = 0 THEN "Done" ELSE "Run"
  /\ UNCHANGED << A, B, Len, merges >>

RecurseSplit ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "Recurse"
       /\ f.lo < f.hi
       /\ LET m == Mid(f.lo, f.hi) IN
            /\ stk' =
                 Push(
                   ReplaceTop(stk,
                     [f EXCEPT !.st = "LeftPending",
                               !.i  = 0,
                               !.j  = 0,
                               !.k  = 0 ]),
                   [ st |-> "Recurse",
                     lo |-> f.lo,
                     hi |-> m,
                     i  |-> 0,
                     j  |-> 0,
                     k  |-> 0 ])
  /\ UNCHANGED << A, B, Len, pc, merges >>

LeftToRight ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "LeftPending"
       /\ LET m == Mid(f.lo, f.hi) IN
            /\ stk' =
                 Push(
                   ReplaceTop(stk,
                     [f EXCEPT !.st = "RightPending" ]),
                   [ st |-> "Recurse",
                     lo |-> m + 1,
                     hi |-> f.hi,
                     i  |-> 0,
                     j  |-> 0,
                     k  |-> 0 ])
  /\ UNCHANGED << A, B, Len, pc, merges >>

RightToCopyL ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN f.st = "RightPending"
  /\ stk' = ReplaceTop(stk, [f EXCEPT !.st = "CopyL", !.i = f.lo ])
  /\ UNCHANGED << A, B, Len, pc, merges >>

CopyLStep ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "CopyL"
       /\ LET m == Mid(f.lo, f.hi) IN
            /\ f.i <= m
            /\ B' = [B EXCEPT ![f.i] = A[f.i]]
            /\ stk' = ReplaceTop(stk, [f EXCEPT !.i = f.i + 1])
  /\ UNCHANGED << A, Len, pc, merges >>

CopyLFinish ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "CopyL"
       /\ LET m == Mid(f.lo, f.hi) IN
            /\ f.i > m
            /\ stk' = ReplaceTop(stk, [f EXCEPT !.st = "CopyR", !.j = m + 1])
  /\ UNCHANGED << A, B, Len, pc, merges >>

CopyRStep ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "CopyR"
       /\ LET m == Mid(f.lo, f.hi) IN
            /\ f.j <= f.hi
            /\ LET dest == f.hi - (f.j - (m + 1)) IN
                 /\ B' = [B EXCEPT ![dest] = A[f.j]]
                 /\ stk' = ReplaceTop(stk, [f EXCEPT !.j = f.j + 1])
  /\ UNCHANGED << A, Len, pc, merges >>

CopyRFinish ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "CopyR"
       /\ f.j > f.hi
       /\ stk' = ReplaceTop(stk, [f EXCEPT !.st = "Merge",
                                            !.i  = f.lo,
                                            !.j  = f.hi,
                                            !.k  = f.lo])
  /\ UNCHANGED << A, B, Len, pc, merges >>

MergeStep ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "Merge"
       /\ f.k <= f.hi
       /\ IF B[f.i] <= B[f.j]
             THEN /\ A' = [A EXCEPT ![f.k] = B[f.i]]
                  /\ stk' = ReplaceTop(stk, [f EXCEPT !.i = f.i + 1,
                                                     !.k = f.k + 1])
             ELSE /\ A' = [A EXCEPT ![f.k] = B[f.j]]
                  /\ stk' = ReplaceTop(stk, [f EXCEPT !.j = f.j - 1,
                                                     !.k = f.k + 1])
       /\ merges' = merges + 1
  /\ UNCHANGED << B, Len, pc >>

MergeFinish ==
  /\ pc = "Run"
  /\ Len(stk) > 0
  /\ LET f == Top(stk) IN
       /\ f.st = "Merge"
       /\ f.k > f.hi
       /\ LET s2 == Pop(stk) IN
            /\ stk' = s2
            /\ pc' = IF Len(s2) = 0 THEN "Done" ELSE "Run"
  /\ UNCHANGED << A, B, Len, merges >>

Next ==
  \/ RecurseDone
  \/ RecurseSplit
  \/ LeftToRight
  \/ RightToCopyL
  \/ CopyLStep
  \/ CopyLFinish
  \/ CopyRStep
  \/ CopyRFinish
  \/ MergeStep
  \/ MergeFinish

vars == << Len, A, B, stk, pc, merges >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Liveness == <> Terminated

=============================================================================
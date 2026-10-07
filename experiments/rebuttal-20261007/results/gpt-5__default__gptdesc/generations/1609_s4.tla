------------------------------ MODULE Quicksort ------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat \ {0}

(*
  Informal description:
  This module models a recursive quicksort over an array A[1..ArrayLen].
  The algorithm uses an explicit control state pc and a stack of procedure
  frames to represent recursive calls to QS(l, r).

  Each frame is a record [l, r, p, stage], where:
    - l, r are the current subarray bounds (indices)
    - p is the chosen pivot index (0 indicates "not chosen yet")
    - stage is one of {"enter","choosePivot","partition","recurseLeft","prepareRight","return"}

  Control flow for a frame f:
    enter:
      if f.l < f.r then go to choosePivot
      else return (pop the frame)
    choosePivot:
      choose p in f.l..f.r; stage := partition
    partition:
      choose a permutation B of A on f.l..f.r that preserves A outside f.l..f.r
      and satisfies the partition property at p, then set A := B; stage := recurseLeft
    recurseLeft:
      set stage := prepareRight and push QS(f.l, p)
    prepareRight:
      if p < r then set stage := return and push QS(p+1, r)
      else set stage := return (no push)
    return:
      pop the frame

  The system terminates when the stack becomes empty and pc = "Done".
*)

(***********************
  Helper definitions
***********************)

S == 1..ArrayLen

StageSet == {"enter","choosePivot","partition","recurseLeft","prepareRight","return"}

FrameSet ==
  [ l : S,
    r : S,
    p : 0..ArrayLen,
    stage : StageSet ]

ReplaceTop(s, f) == Append(SubSeq(s, 1, Len(s)-1), f)

Pop(s) == SubSeq(s, 1, Len(s)-1)

Push(s, f) == Append(s, f)

IsInj(π, S0) == \A i,j \in S0: (π[i] = π[j]) => i = j

IsSurj(π, S0) == \A k \in S0: \E i \in S0: π[i] = k

Bij(π, S0) == (π \in [S0 -> S0]) /\ IsInj(π, S0) /\ IsSurj(π, S0)

Permutation(A,B) ==
  \E π \in [S -> S]:
    Bij(π, S) /\ \A i \in S: A[i] = B[π[i]]

SubPerm(A,B,l,r) ==
  LET R == l..r IN
    \E π \in [R -> R]:
      Bij(π, R) /\ \A i \in R: B[i] = A[π[i]]

PartitionOK(A,B,l,r,p) ==
  /\ B \in [S -> Int]
  /\ \A i \in S \ (l..r): B[i] = A[i]
  /\ SubPerm(A,B,l,r)
  /\ \A i \in l..p: \A j \in (p+1)..r: B[i] <= B[j]

Sorted(A) ==
  \A i, j \in S: i <= j => A[i] <= A[j]

FrameOK(f) ==
  /\ f \in FrameSet
  /\ (f.p = 0) \/ (f.l <= f.p /\ f.p <= f.r)

StackOK(stk) ==
  /\ stk \in Seq(FrameSet)
  /\ \A k \in 1..Len(stk): FrameOK(stk[k])

(***********************
  State variables
***********************)

VARIABLES
  A,        \* current array (function 1..ArrayLen -> Int)
  AInit,    \* initial array, kept constant
  pc,       \* control state: "Run" or "Done"
  stack     \* sequence of frames implementing recursion

vars == << A, AInit, pc, stack >>

(***********************
  Initialization
***********************)

Init ==
  /\ A \in [S -> Int]
  /\ AInit = A
  /\ stack = << [l |-> 1, r |-> ArrayLen, p |-> 0, stage |-> "enter"] >>
  /\ pc = "Run"

(***********************
  Transition relation
***********************)

EnterAdvance ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "enter"
       /\ top.l < top.r
       /\ stack' = ReplaceTop(stack, [l |-> top.l, r |-> top.r, p |-> 0, stage |-> "choosePivot"])
       /\ A' = A
       /\ AInit' = AInit
       /\ pc' = "Run"

BasePop ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "enter"
       /\ top.l >= top.r
       /\ stack' = Pop(stack)
       /\ A' = A
       /\ AInit' = AInit
       /\ pc' = IF Len(stack') = 0 THEN "Done" ELSE "Run"

ChoosePivotAct ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "choosePivot"
       /\ \E piv \in top.l..top.r:
            /\ stack' = ReplaceTop(stack, [l |-> top.l, r |-> top.r, p |-> piv, stage |-> "partition"])
            /\ A' = A
            /\ AInit' = AInit
            /\ pc' = "Run"

PartitionAct ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "partition"
       /\ \E B \in [S -> Int]:
            /\ PartitionOK(A, B, top.l, top.r, top.p)
            /\ A' = B
            /\ stack' = ReplaceTop(stack, [l |-> top.l, r |-> top.r, p |-> top.p, stage |-> "recurseLeft"])
            /\ AInit' = AInit
            /\ pc' = "Run"

RecurseLeftPush ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "recurseLeft"
       /\ LET parent' == [l |-> top.l, r |-> top.r, p |-> top.p, stage |-> "prepareRight"] IN
          LET left   == [l |-> top.l, r |-> top.p, p |-> 0,      stage |-> "enter"] IN
            /\ stack' = Push(ReplaceTop(stack, parent'), left)
            /\ A' = A
            /\ AInit' = AInit
            /\ pc' = "Run"

PushRightPush ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "prepareRight"
       /\ top.p < top.r
       /\ LET parent' == [l |-> top.l,     r |-> top.r,     p |-> top.p,      stage |-> "return"] IN
          LET right  == [l |-> top.p + 1,  r |-> top.r,     p |-> 0,          stage |-> "enter"] IN
            /\ stack' = Push(ReplaceTop(stack, parent'), right)
            /\ A' = A
            /\ AInit' = AInit
            /\ pc' = "Run"

PushRightNoPush ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "prepareRight"
       /\ top.p >= top.r
       /\ stack' = ReplaceTop(stack, [l |-> top.l, r |-> top.r, p |-> top.p, stage |-> "return"])
       /\ A' = A
       /\ AInit' = AInit
       /\ pc' = "Run"

ReturnPop ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
       /\ top.stage = "return"
       /\ stack' = Pop(stack)
       /\ A' = A
       /\ AInit' = AInit
       /\ pc' = IF Len(stack') = 0 THEN "Done" ELSE "Run"

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  EnterAdvance
  \/ BasePop
  \/ ChoosePivotAct
  \/ PartitionAct
  \/ RecurseLeftPush
  \/ PushRightPush
  \/ PushRightNoPush
  \/ ReturnPop
  \/ DoneStutter

(***********************
  Invariants and properties
***********************)

TypeInv ==
  /\ A \in [S -> Int]
  /\ AInit \in [S -> Int]
  /\ pc \in {"Run","Done"}
  /\ StackOK(stack)

PermInv ==
  Permutation(A, AInit)

PostCondition ==
  (pc = "Done") => (Sorted(A) /\ Permutation(A, AInit))

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Termination ==
  <> (pc = "Done")

=============================================================================
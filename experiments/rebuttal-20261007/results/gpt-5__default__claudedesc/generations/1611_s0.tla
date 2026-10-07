------------------------------ MODULE MergeSortSpec ------------------------------

EXTENDS Naturals, Integers, Sequences, TLC

CONSTANT ArrayLen

VARIABLES N, a, b, stack, pc

Phases == {"split", "left", "right", "copyL", "copyR", "merge"}

Frame(l, r) ==
  [ l |-> l,
    r |-> r,
    m |-> 0,
    i |-> 0,
    j |-> 0,
    k |-> 0,
    phase |-> "split"
  ]

Vars == << N, a, b, stack, pc >>

Init ==
  /\ \E n \in 0..ArrayLen:
       \E aa \in [1..n -> 1..n]:
       \E bb \in [1..n -> 1..n]:
         /\ N = n
         /\ a = aa
         /\ b = bb
  /\ stack = << >>
  /\ pc = "Start"

StartStep ==
  /\ pc = "Start"
  /\ IF N <= 1
     THEN /\ pc' = "Done"
          /\ UNCHANGED << N, a, b, stack >>
     ELSE /\ stack' = Append(stack, Frame(1, N))
          /\ pc' = "Run"
          /\ UNCHANGED << N, a, b >>

FinishRunStep ==
  /\ pc = "Run"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << N, a, b, stack >>

PopBaseStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "split"
        /\ t.l >= t.r
        /\ stack' = stack[1..Len(stack)-1]
  /\ UNCHANGED << N, a, b, pc >>

SplitLeftStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
         m == (t.l + t.r) \div 2
     IN /\ t.phase = "split"
        /\ t.l < t.r
        /\ stack' =
             Append(
               [ stack EXCEPT ![Len(stack)] = [@ EXCEPT !.m = m, !.phase = "left"] ],
               Frame(t.l, m)
             )
  /\ UNCHANGED << N, a, b, pc >>

PushRightStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "left"
        /\ stack' =
             Append(
               [ stack EXCEPT ![Len(stack)] = [@ EXCEPT !.phase = "right"] ],
               Frame(t.m + 1, t.r)
             )
  /\ UNCHANGED << N, a, b, pc >>

PrepCopyLeftStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "right"
        /\ stack' =
             [ stack EXCEPT ![Len(stack)] =
                 [ @ EXCEPT !.phase = "copyL", !.i = @.l ]
             ]
  /\ UNCHANGED << N, a, b, pc >>

CopyLeftIterStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "copyL"
        /\ t.i <= t.m
        /\ b' = [ b EXCEPT ![t.i] = a[t.i] ]
        /\ stack' = [ stack EXCEPT ![Len(stack)] = [@ EXCEPT !.i = t.i + 1] ]
        /\ UNCHANGED << N, a, pc >>

CopyLeftDoneStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "copyL"
        /\ t.i > t.m
        /\ stack' =
             [ stack EXCEPT ![Len(stack)] =
                 [ @ EXCEPT
                     !.phase = "copyR",
                     !.i = @.m + 1,
                     !.j = @.r
                 ]
             ]
        /\ UNCHANGED << N, a, b, pc >>

CopyRightIterStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "copyR"
        /\ t.i <= t.r
        /\ b' = [ b EXCEPT ![t.i] = a[t.j] ]
        /\ stack' =
             [ stack EXCEPT ![Len(stack)] =
                 [ @ EXCEPT
                     !.i = t.i + 1,
                     !.j = t.j - 1
                 ]
             ]
        /\ UNCHANGED << N, a, pc >>

CopyRightDoneStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "copyR"
        /\ t.i > t.r
        /\ stack' =
             [ stack EXCEPT ![Len(stack)] =
                 [ @ EXCEPT
                     !.phase = "merge",
                     !.i = @.l,
                     !.j = @.r,
                     !.k = @.l
                 ]
             ]
        /\ UNCHANGED << N, a, b, pc >>

MergeIterStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "merge"
        /\ t.k <= t.r
        /\ IF b[t.i] <= b[t.j]
           THEN /\ a' = [ a EXCEPT ![t.k] = b[t.i] ]
                /\ stack' =
                     [ stack EXCEPT ![Len(stack)] =
                         [ @ EXCEPT
                             !.i = t.i + 1,
                             !.k = t.k + 1
                         ]
                     ]
           ELSE /\ a' = [ a EXCEPT ![t.k] = b[t.j] ]
                /\ stack' =
                     [ stack EXCEPT ![Len(stack)] =
                         [ @ EXCEPT
                             !.j = t.j - 1,
                             !.k = t.k + 1
                         ]
                     ]
        /\ UNCHANGED << N, b, pc >>

MergeDoneStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET t == stack[Len(stack)]
     IN /\ t.phase = "merge"
        /\ t.k > t.r
        /\ stack' = stack[1..Len(stack)-1]
  /\ UNCHANGED << N, a, b, pc >>

Next ==
  \/ StartStep
  \/ FinishRunStep
  \/ PopBaseStep
  \/ SplitLeftStep
  \/ PushRightStep
  \/ PrepCopyLeftStep
  \/ CopyLeftIterStep
  \/ CopyLeftDoneStep
  \/ CopyRightIterStep
  \/ CopyRightDoneStep
  \/ MergeIterStep
  \/ MergeDoneStep

IsSorted(arr) ==
  \A i, j \in 1..N : (i < j) => arr[i] <= arr[j]

Invariant ==
  (pc # "Done") \/ IsSorted(a)

Termination ==
  <> (pc = "Done")

PossibleCounts ==
  TRUE

Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(Next)

=============================================================================
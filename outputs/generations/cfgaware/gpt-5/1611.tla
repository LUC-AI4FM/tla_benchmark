--------------------------- MODULE MergesortStack ---------------------------
EXTENDS Integers, Sequences

CONSTANTS
  defaultInitValue,
  ArrayLen

(*
  Recursive mergesort encoded with an explicit call stack.
  Values are in 1..N where N == ArrayLen, and the input length is any len in 0..ArrayLen.
*)

N == ArrayLen

VARIABLES
  a,        \* array to sort: function 1..len -> 1..N
  b,        \* auxiliary buffer: function 1..len -> 1..N
  len,      \* actual length, in 0..ArrayLen
  stack,    \* explicit call stack, a sequence of frames (records)
  pc        \* program counter: "Run" or "Done"

vars == << a, b, len, stack, pc >>

\* Frame schema
Frame ==
  [ l     : Nat,
    r     : Nat,
    phase : {"enter","afterLeft","afterRight","merge","copyBack"},
    m     : Nat,
    i     : Nat,
    j     : Nat,
    k     : Nat ]

Top(s)  == s[Len(s)]
Rest(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 1, Len(s)-1)

IsSorted(arr, n) ==
  \A i, j \in 1..n : i <= j => arr[i] <= arr[j]

TypeInv ==
  /\ len \in Nat /\ len <= ArrayLen
  /\ a \in [1..len -> 1..N]
  /\ b \in [1..len -> 1..N]
  /\ pc \in {"Run","Done"}
  /\ stack \in Seq(Frame)

Init ==
  /\ len \in 0..ArrayLen
  /\ a \in [1..len -> 1..N]
  /\ b = a
  /\ pc = "Run"
  /\ stack =
        IF len = 0
        THEN << >>
        ELSE << [ l |-> 1, r |-> len, phase |-> "enter",
                  m |-> 0, i |-> 0, j |-> 0, k |-> 0 ] >>

\* Actions operating on the top frame
EnterBase ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
     IN /\ fr.phase = "enter"
        /\ fr.l >= fr.r
        /\ stack' = rs
        /\ UNCHANGED << a, b, len, pc >>

EnterRecurse ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         mid == (fr.l + fr.r) \div 2
         top1 == [fr EXCEPT !.phase = "afterLeft", !.m = mid]
         left == [ l |-> fr.l, r |-> mid, phase |-> "enter",
                   m |-> 0, i |-> 0, j |-> 0, k |-> 0 ]
     IN /\ fr.phase = "enter"
        /\ fr.l < fr.r
        /\ stack' = rs \o << top1, left >>
        /\ UNCHANGED << a, b, len, pc >>

AfterLeft ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         top1 == [fr EXCEPT !.phase = "afterRight"]
         right == [ l |-> fr.m + 1, r |-> fr.r, phase |-> "enter",
                    m |-> 0, i |-> 0, j |-> 0, k |-> 0 ]
     IN /\ fr.phase = "afterLeft"
        /\ stack' = rs \o << top1, right >>
        /\ UNCHANGED << a, b, len, pc >>

AfterRight ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         top1 == [fr EXCEPT !.phase = "merge",
                          !.i = fr.l, !.j = fr.m + 1, !.k = fr.l]
     IN /\ fr.phase = "afterRight"
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << a, b, len, pc >>

MergeLeftTake ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         cond == fr.i <= fr.m /\ fr.j <= fr.r
         top1 == [fr EXCEPT !.i = fr.i + 1, !.k = fr.k + 1]
     IN /\ fr.phase = "merge"
        /\ cond
        /\ a[fr.i] <= a[fr.j]
        /\ b' = [b EXCEPT ![fr.k] = a[fr.i]]
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << a, len, pc >>

MergeRightTake ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         cond == fr.i <= fr.m /\ fr.j <= fr.r
         top1 == [fr EXCEPT !.j = fr.j + 1, !.k = fr.k + 1]
     IN /\ fr.phase = "merge"
        /\ cond
        /\ a[fr.i] > a[fr.j]
        /\ b' = [b EXCEPT ![fr.k] = a[fr.j]]
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << a, len, pc >>

MergeCopyLeft ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         top1 == [fr EXCEPT !.i = fr.i + 1, !.k = fr.k + 1]
     IN /\ fr.phase = "merge"
        /\ fr.i <= fr.m /\ fr.j > fr.r
        /\ b' = [b EXCEPT ![fr.k] = a[fr.i]]
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << a, len, pc >>

MergeCopyRight ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         top1 == [fr EXCEPT !.j = fr.j + 1, !.k = fr.k + 1]
     IN /\ fr.phase = "merge"
        /\ fr.j <= fr.r /\ fr.i > fr.m
        /\ b' = [b EXCEPT ![fr.k] = a[fr.j]]
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << a, len, pc >>

MergeDone ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         top1 == [fr EXCEPT !.phase = "copyBack", !.i = fr.l]
     IN /\ fr.phase = "merge"
        /\ fr.i > fr.m /\ fr.j > fr.r
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << a, b, len, pc >>

CopyBackStep ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
         top1 == [fr EXCEPT !.i = fr.i + 1]
     IN /\ fr.phase = "copyBack"
        /\ fr.i <= fr.r
        /\ a' = [a EXCEPT ![fr.i] = b[fr.i]]
        /\ stack' = rs \o << top1 >>
        /\ UNCHANGED << b, len, pc >>

CopyBackDone ==
  /\ pc = "Run"
  /\ stack # << >>
  /\ LET fr == Top(stack)
         rs == Rest(stack)
     IN /\ fr.phase = "copyBack"
        /\ fr.i > fr.r
        /\ stack' = rs
        /\ UNCHANGED << a, b, len, pc >>

Finish ==
  /\ pc = "Run"
  /\ stack = << >>
  /\ pc' = "Done"
  /\ UNCHANGED << a, b, len, stack >>

Next ==
  EnterBase
  \/ EnterRecurse
  \/ AfterLeft
  \/ AfterRight
  \/ MergeLeftTake
  \/ MergeRightTake
  \/ MergeCopyLeft
  \/ MergeCopyRight
  \/ MergeDone
  \/ CopyBackStep
  \/ CopyBackDone
  \/ Finish

Spec == Init /\ [][Next]_vars

Invariant == TypeInv /\ (pc # "Done" \/ IsSorted(a, len))

Termination == WF_vars(Next) => <> (pc = "Done")
=============================================================================
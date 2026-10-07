----------------------------- MODULE MergeSortSpec -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, ArrayLen

VARIABLES a, b, len, pc, stack

Domain == 1..len

Stages == {"call", "afterLeft", "afterRight", "merge", "mergeI"}

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)
ReplaceTop(s, x) == Append(SubSeq(s, 1, Len(s) - 1), x)
Push(s, x) == Append(s, x)

Mid(l, r) == (l + r) \div 2

IsSorted(arr, n) ==
  \A i, j \in 1..n: i <= j => arr[i] <= arr[j]

TypeOK ==
  /\ len \in 0..ArrayLen
  /\ a \in [Domain -> 1..N]
  /\ b \in [Domain -> 1..N]
  /\ pc \in {"Run", "Done"}
  /\ stack \in Seq([ l     : Domain,
                      r     : Domain,
                      m     : 0..len,
                      stage : Stages,
                      i     : 0..(len+1),
                      j     : 0..(len+1),
                      k     : 0..(len+1) ])

DoneImpliesSorted == pc = "Done" => IsSorted(a, len)

Safety == [](pc = "Done" => IsSorted(a, len))

Termination == <>(pc = "Done")

Init ==
  /\ len \in 0..ArrayLen
  /\ a \in [Domain -> 1..N]
  /\ b \in [Domain -> 1..N]
  /\ IF len <= 1
        THEN /\ pc = "Done"
             /\ stack = << >>
        ELSE /\ pc = "Run"
             /\ stack = << [ l |-> 1,
                              r |-> len,
                              m |-> 0,
                              stage |-> "call",
                              i |-> 0, j |-> 0, k |-> 0 ] >>

Term ==
  /\ pc = "Run"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << a, b, len, stack >>

CallBase ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.stage = "call"
       /\ f.l >= f.r
       /\ stack' = Pop(stack)
  /\ UNCHANGED << a, b, len, pc >>

CallSplit ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.stage = "call"
       /\ f.l < f.r
       /\ LET m == Mid(f.l, f.r) IN
            /\ stack' =
                 Push(
                   ReplaceTop(stack, [f EXCEPT !.stage = "afterLeft", !.m = m]),
                   [ l |-> f.l, r |-> m, m |-> 0, stage |-> "call", i |-> 0, j |-> 0, k |-> 0 ]
                 )
  /\ UNCHANGED << a, b, len, pc >>

AfterLeftStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.stage = "afterLeft"
       /\ stack' =
            Push(
              ReplaceTop(stack, [f EXCEPT !.stage = "afterRight"]),
              [ l |-> f.m + 1, r |-> f.r, m |-> 0, stage |-> "call", i |-> 0, j |-> 0, k |-> 0 ]
            )
  /\ UNCHANGED << a, b, len, pc >>

AfterRightToMerge ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.stage = "afterRight"
       /\ stack' = ReplaceTop(stack, [f EXCEPT !.stage = "merge"])
  /\ UNCHANGED << a, b, len, pc >>

MergePrep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.stage = "merge"
       /\ LET l == f.l IN
          LET r == f.r IN
          LET m == f.m IN
             /\ b' = [ i \in Domain |-> IF l <= i /\ i <= r THEN a[i] ELSE b[i] ]
             /\ stack' = ReplaceTop(stack, [f EXCEPT !.stage = "mergeI", !.i = l, !.j = m+1, !.k = l])
  /\ UNCHANGED << a, len, pc >>

MergeStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
       /\ f.stage = "mergeI"
       /\ LET l  == f.l IN
          LET r  == f.r IN
          LET m  == f.m IN
          LET i0 == f.i IN
          LET j0 == f.j IN
          LET k0 == f.k IN
             /\ IF k0 > r THEN
                   /\ stack' = Pop(stack)
                   /\ UNCHANGED << a, b, len, pc >>
                ELSE IF i0 > m THEN
                   /\ a' = [ a EXCEPT ![k0] = b[j0] ]
                   /\ stack' = ReplaceTop(stack, [f EXCEPT !.i = i0, !.j = j0 + 1, !.k = k0 + 1])
                   /\ UNCHANGED << b, len, pc >>
                ELSE IF j0 > r THEN
                   /\ a' = [ a EXCEPT ![k0] = b[i0] ]
                   /\ stack' = ReplaceTop(stack, [f EXCEPT !.i = i0 + 1, !.j = j0, !.k = k0 + 1])
                   /\ UNCHANGED << b, len, pc >>
                ELSE IF b[i0] <= b[j0] THEN
                   /\ a' = [ a EXCEPT ![k0] = b[i0] ]
                   /\ stack' = ReplaceTop(stack, [f EXCEPT !.i = i0 + 1, !.j = j0, !.k = k0 + 1])
                   /\ UNCHANGED << b, len, pc >>
                ELSE
                   /\ a' = [ a EXCEPT ![k0] = b[j0] ]
                   /\ stack' = ReplaceTop(stack, [f EXCEPT !.i = i0, !.j = j0 + 1, !.k = k0 + 1])
                   /\ UNCHANGED << b, len, pc >>

Next == Term \/ CallBase \/ CallSplit \/ AfterLeftStep \/ AfterRightToMerge \/ MergePrep \/ MergeStep

vars == << a, b, len, pc, stack >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
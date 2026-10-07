---------------------------- MODULE QuickSortPlusCal ----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS ArrayLen

ASSUME ArrayLen \in Nat \ {0}

VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

Indices == 1..ArrayLen
Values  == 1..ArrayLen

Labels == {"main", "qs1", "qs2", "qs3", "qs4", "test", "Done"}

Range(lo, hi) == { i \in Indices : lo <= i /\ i <= hi }

CountIn(Ary, S, v) == Cardinality({ i \in S : Ary[i] = v })

UnchangedOutside(Ap, A0, lo, hi) ==
  LET S == Range(lo, hi) IN \A i \in (Indices \ S) : Ap[i] = A0[i]

PermWithin(Ap, A0, lo, hi) ==
  LET S == Range(lo, hi) IN \A v \in Values : CountIn(Ap, S, v) = CountIn(A0, S, v)

PartitionOK(Ap, lo, hi, p) ==
  /\ p \in Range(lo, hi)
  /\ \A i \in Range(lo, p) : \A j \in Range(p+1, hi) : Ap[i] <= Ap[j]

Permutation(A1, A2) == \A v \in Values : CountIn(A1, Indices, v) = CountIn(A2, Indices, v)

Sorted(Ary) == \A i, j \in Indices : (i < j) => Ary[i] <= Ary[j]

FrameType == [retpc : Labels, qlo : 1..(ArrayLen + 1), qhi : 0..ArrayLen, pivot : 0..ArrayLen]

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)

TypeOK ==
  /\ Ainit \in [Indices -> Values]
  /\ A \in [Indices -> Values]
  /\ pc \in Labels
  /\ stack \in Seq(FrameType)
  /\ qlo \in 1..(ArrayLen + 1)
  /\ qhi \in 0..ArrayLen
  /\ pivot \in 0..ArrayLen

PermInv == Permutation(A, Ainit)

Init ==
  /\ Ainit \in [Indices -> Values]
  /\ A = Ainit
  /\ pc = "main"
  /\ stack = << >>
  /\ qlo = 1
  /\ qhi = ArrayLen
  /\ pivot = 0

Main ==
  /\ pc = "main"
  /\ stack' = << >>
  /\ qlo' = 1
  /\ qhi' = ArrayLen
  /\ pc' = "qs1"
  /\ UNCHANGED << Ainit, A, pivot >>

QS1 ==
  /\ pc = "qs1"
  /\ IF qlo < qhi THEN
       \E p, Ap :
         /\ p \in Range(qlo, qhi)
         /\ Ap \in [Indices -> Values]
         /\ UnchangedOutside(Ap, A, qlo, qhi)
         /\ PermWithin(Ap, A, qlo, qhi)
         /\ PartitionOK(Ap, qlo, qhi, p)
         /\ A' = Ap
         /\ pivot' = p
         /\ pc' = "qs2"
         /\ UNCHANGED << Ainit, stack, qlo, qhi >>
     ELSE
       /\ pc' = "qs4"
       /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

QS2 ==
  /\ pc = "qs2"
  /\ stack' = Append(stack, [retpc |-> "qs3", qlo |-> qlo, qhi |-> qhi, pivot |-> pivot])
  /\ qlo' = qlo
  /\ qhi' = pivot
  /\ pc' = "qs1"
  /\ UNCHANGED << Ainit, A, pivot >>

QS3 ==
  /\ pc = "qs3"
  /\ stack' = Append(stack, [retpc |-> "qs4", qlo |-> qlo, qhi |-> qhi, pivot |-> pivot])
  /\ qlo' = pivot + 1
  /\ qhi' = qhi
  /\ pc' = "qs1"
  /\ UNCHANGED << Ainit, A, pivot >>

QS4 ==
  /\ pc = "qs4"
  /\ IF Len(stack) > 0 THEN
       LET f == Top(stack) IN
         /\ stack' = Pop(stack)
         /\ qlo' = f.qlo
         /\ qhi' = f.qhi
         /\ pivot' = f.pivot
         /\ pc' = f.retpc
         /\ UNCHANGED << Ainit, A >>
     ELSE
       /\ pc' = "test"
       /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

Test ==
  /\ pc = "test"
  /\ Permutation(A, Ainit)
  /\ Sorted(A)
  /\ pc' = "Done"
  /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

Next == Main \/ QS1 \/ QS2 \/ QS3 \/ QS4 \/ Test

vars == << Ainit, A, pc, stack, qlo, qhi, pivot >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

=============================================================================
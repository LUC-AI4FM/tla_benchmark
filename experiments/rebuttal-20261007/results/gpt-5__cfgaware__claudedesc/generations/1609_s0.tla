----------------------------- MODULE Quicksort -----------------------------
EXTENDS Naturals, Integers, Sequences

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

(*
  Informal PlusCal sketch (not executed; TLA+ below is authoritative):

  --algorithm QSAlgo
  variables Ainit \in [1..ArrayLen -> 1..ArrayLen], A = Ainit,
            pc = "main", stack = << >>, qlo, qhi, pivot;
  define
    ArrLen(arr) == ArrayLen;
  end define;
  begin
  main:
    stack := Append(stack, [retpc |-> "test", qlo |-> 0, qhi |-> 0]);
    qlo := 1; qhi := ArrLen(A);
    goto qs1;
  qs1:
    if qlo >= qhi then
      goto qs4;
    else
      with pv \in qlo..qhi, Anew \in [1..ArrayLen -> 1..ArrayLen] do
        assume \A k \in 1..ArrayLen: (k \in qlo..qhi) \/ (Anew[k] = A[k]);
        assume Partition(Anew, qlo, pv, qhi);
        assume IsPermutation(Anew, A);
        A := Anew; pivot := pv;
      end with;
      goto qs2;
    end if;
  qs2:
    stack := Append(stack, [retpc |-> "qs3", qlo |-> pivot+1, qhi |-> qhi]);
    qhi := pivot;
    goto qs1;
  qs3:
    goto qs1;
  qs4:
    with top = stack[Len(stack)] do
      pc := top.retpc; qlo := top.qlo; qhi := top.qhi;
      stack := SubSeq(stack, 1, Len(stack)-1);
    end with;
  test:
    assert IsPermutation(A, Ainit) /\ Sorted(A);
    goto Done;
  Done:
    skip;
  end algorithm
*)

VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

Dom == 1..ArrayLen

ArrLen(arr) == ArrayLen

Partition(arr, lo, piv, hi) ==
  \A i \in (lo..piv): \A j \in ((piv + 1)..hi): arr[i] <= arr[j]

Sorted(arr) ==
  \A i, j \in Dom: (i < j) => arr[i] <= arr[j]

IsPermutation(B, A) ==
  \E p \in [Dom -> Dom]:
    /\ \A x, y \in Dom: (x # y) => (p[x] # p[y])
    /\ \A y \in Dom: \E x \in Dom: p[x] = y
    /\ \A i \in Dom: B[i] = A[p[i]]

Vars == << Ainit, A, pc, stack, qlo, qhi, pivot >>

Init ==
  /\ Ainit \in [Dom -> Dom]
  /\ A = Ainit
  /\ pc = "main"
  /\ stack = << >>
  /\ qlo \in Int
  /\ qhi \in Int
  /\ pivot \in Int

Main ==
  /\ pc = "main"
  /\ stack' = Append(stack, [retpc |-> "test", qlo |-> 0, qhi |-> 0])
  /\ qlo' = 1
  /\ qhi' = ArrLen(A)
  /\ pc' = "qs1"
  /\ UNCHANGED << Ainit, A, pivot >>

Qs1Base ==
  /\ pc = "qs1"
  /\ qlo >= qhi
  /\ pc' = "qs4"
  /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

Qs1Part ==
  /\ pc = "qs1"
  /\ qlo < qhi
  /\ \E pv \in qlo..qhi, Anew \in [Dom -> Dom]:
       /\ \A k \in Dom: (k \in qlo..qhi) \/ (Anew[k] = A[k])
       /\ IsPermutation(Anew, A)
       /\ Partition(Anew, qlo, pv, qhi)
       /\ A' = Anew
       /\ pivot' = pv
       /\ pc' = "qs2"
       /\ UNCHANGED << Ainit, stack, qlo, qhi >>

Qs2 ==
  /\ pc = "qs2"
  /\ stack' = Append(stack, [retpc |-> "qs3", qlo |-> (pivot + 1), qhi |-> qhi])
  /\ qhi' = pivot
  /\ pc' = "qs1"
  /\ UNCHANGED << Ainit, A, qlo, pivot >>

Qs3 ==
  /\ pc = "qs3"
  /\ pc' = "qs1"
  /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

Qs4 ==
  /\ pc = "qs4"
  /\ Len(stack) >= 1
  /\ LET n == Len(stack) IN
     LET top == stack[n] IN
       /\ pc' = top.retpc
       /\ qlo' = top.qlo
       /\ qhi' = top.qhi
       /\ stack' = SubSeq(stack, 1, n - 1)
       /\ UNCHANGED << Ainit, A, pivot >>

Test ==
  /\ pc = "test"
  /\ IsPermutation(A, Ainit)
  /\ Sorted(A)
  /\ pc' = "Done"
  /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

DoneAction ==
  /\ pc = "Done"
  /\ UNCHANGED Vars

Next == Main \/ Qs1Base \/ Qs1Part \/ Qs2 \/ Qs3 \/ Qs4 \/ Test \/ DoneAction

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

Termination == <> (pc = "Done")

============================================================================
---------------------------- MODULE MergeSort ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, ArrayLen

ASSUME N \in Nat /\ N >= 1
ASSUME ArrayLen \in Nat

(***************************************************************************
--algorithm MergeSort {
  variables a \in UNION {[1..n -> 1..N] : n \in 0..ArrayLen}, b = a;

  procedure mergesort(lo, hi)
    variables mid = 0, i = 0, j = 0, k = 0;
  {
   ms1: if (lo < hi) {
          mid := (lo + hi) \div 2;
          call mergesort(lo, mid);
        } else { return; };
   ms2: call mergesort(mid + 1, hi);
   ms3: i := lo; j := mid + 1; k := lo;
   ms4: while (k <= hi) {
          if (i <= mid /\ (j > hi \/ a[i] <= a[j])) {
            b[k] := a[i]; i := i + 1;
          } else {
            b[k] := a[j]; j := j + 1;
          };
          k := k + 1;
        };
        k := lo;
   ms5: while (k <= hi) {
          a[k] := b[k]; k := k + 1;
        };
        return;
  }

  {
   main: call mergesort(1, Len(a));
  }
}
***************************************************************************)

VARIABLES a, b, pc, stack, lo, hi, mid, i, j, k

vars == << a, b, pc, stack, lo, hi, mid, i, j, k >>

Frame(retpc) ==
    [ procedure |-> "mergesort",
      pc        |-> retpc,
      lo        |-> lo,
      hi        |-> hi,
      mid       |-> mid,
      i         |-> i,
      j         |-> j,
      k         |-> k ]

Init ==
    /\ a \in UNION {[1..n -> 1..N] : n \in 0..ArrayLen}
    /\ b = a
    /\ stack = << >>
    /\ lo = 0
    /\ hi = 0
    /\ mid = 0
    /\ i = 0
    /\ j = 0
    /\ k = 0
    /\ pc = "main"

\* Return from the current mergesort invocation, restoring caller's frame
Return ==
    /\ pc'    = Head(stack).pc
    /\ lo'    = Head(stack).lo
    /\ hi'    = Head(stack).hi
    /\ mid'   = Head(stack).mid
    /\ i'     = Head(stack).i
    /\ j'     = Head(stack).j
    /\ k'     = Head(stack).k
    /\ stack' = Tail(stack)

main ==
    /\ pc = "main"
    /\ stack' = << Frame("Done") >> \o stack
    /\ lo' = 1
    /\ hi' = Len(a)
    /\ mid' = 0
    /\ i' = 0
    /\ j' = 0
    /\ k' = 0
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

ms1 ==
    /\ pc = "ms1"
    /\ IF lo < hi
         THEN LET m == (lo + hi) \div 2 IN
              /\ stack' = << [ procedure |-> "mergesort",
                               pc        |-> "ms2",
                               lo        |-> lo,
                               hi        |-> hi,
                               mid       |-> m,
                               i         |-> i,
                               j         |-> j,
                               k         |-> k ] >> \o stack
              /\ lo' = lo
              /\ hi' = m
              /\ mid' = 0
              /\ i' = 0
              /\ j' = 0
              /\ k' = 0
              /\ pc' = "ms1"
         ELSE Return
    /\ UNCHANGED << a, b >>

ms2 ==
    /\ pc = "ms2"
    /\ stack' = << Frame("ms3") >> \o stack
    /\ lo' = mid + 1
    /\ hi' = hi
    /\ mid' = 0
    /\ i' = 0
    /\ j' = 0
    /\ k' = 0
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

ms3 ==
    /\ pc = "ms3"
    /\ i' = lo
    /\ j' = mid + 1
    /\ k' = lo
    /\ pc' = "ms4"
    /\ UNCHANGED << a, b, stack, lo, hi, mid >>

ms4 ==
    /\ pc = "ms4"
    /\ IF k <= hi
         THEN /\ IF i <= mid /\ (j > hi \/ a[i] <= a[j])
                   THEN /\ b' = [b EXCEPT ![k] = a[i]]
                        /\ i' = i + 1
                        /\ j' = j
                   ELSE /\ b' = [b EXCEPT ![k] = a[j]]
                        /\ j' = j + 1
                        /\ i' = i
              /\ k' = k + 1
              /\ pc' = "ms4"
         ELSE /\ k' = lo
              /\ pc' = "ms5"
              /\ UNCHANGED << b, i, j >>
    /\ UNCHANGED << a, stack, lo, hi, mid >>

ms5 ==
    /\ pc = "ms5"
    /\ IF k <= hi
         THEN /\ a' = [a EXCEPT ![k] = b[k]]
              /\ k' = k + 1
              /\ pc' = "ms5"
              /\ UNCHANGED << stack, lo, hi, mid, i, j >>
         ELSE /\ Return
              /\ UNCHANGED a
    /\ UNCHANGED b

mergesort == ms1 \/ ms2 \/ ms3 \/ ms4 \/ ms5

\* Allow infinite stuttering to prevent deadlock on termination
Terminating == pc = "Done" /\ UNCHANGED vars

Next == main \/ mergesort \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
\* Safety: upon termination, the array is sorted in nondecreasing order
Sorted(arr) == \A x, y \in 1..Len(arr) : x < y => arr[x] <= arr[y]

SortedAtDone == pc = "Done" => Sorted(a)

TypeOK ==
    /\ a \in UNION {[1..n -> 1..N] : n \in 0..ArrayLen}
    /\ DOMAIN b = DOMAIN a
    /\ lo \in Nat /\ hi \in Nat /\ mid \in Nat
    /\ i \in Nat /\ j \in Nat /\ k \in Nat
    /\ pc \in {"main", "ms1", "ms2", "ms3", "ms4", "ms5", "Done"}

THEOREM Spec => [](TypeOK /\ SortedAtDone)
THEOREM Spec => Termination
=============================================================================
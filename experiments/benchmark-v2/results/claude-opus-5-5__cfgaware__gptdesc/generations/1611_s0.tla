---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS defaultInitValue, ArrayLen

N == 3

(***************************************************************************
--algorithm MergeSort {
  variables a \in UNION {[1..n -> 1..N] : n \in 0..ArrayLen},
            b = a;

  procedure mergesort(lo, hi)
    variables mid = defaultInitValue, i = defaultInitValue,
              j = defaultInitValue, k = defaultInitValue; {
   ms1:  if (lo < hi) {
           mid := (lo + hi) \div 2;
   ms1a:   call mergesort(lo, mid);
   ms2:    call mergesort(mid + 1, hi);
   ms3:    i := lo; j := mid + 1; k := lo;
   ms4:    while (k <= hi) {
             if (i <= mid /\ (j > hi \/ a[i] <= a[j])) {
               b[k] := a[i]; i := i + 1
             } else {
               b[k] := a[j]; j := j + 1
             };
             k := k + 1
           };
   ms5:    k := lo;
   ms6:    while (k <= hi) {
             a[k] := b[k]; k := k + 1
           }
         };
   ret:  return
  }

  {
   Lbl_1: call mergesort(1, Len(a))
  }
}
***************************************************************************)

VARIABLES a, b, pc, stack, lo, hi, mid, i, j, k

vars == << a, b, pc, stack, lo, hi, mid, i, j, k >>

Init ==
    /\ a \in UNION {[1..n -> 1..N] : n \in 0..ArrayLen}
    /\ b = a
    /\ lo = defaultInitValue
    /\ hi = defaultInitValue
    /\ mid = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue
    /\ stack = << >>
    /\ pc = "Lbl_1"

ms1 ==
    /\ pc = "ms1"
    /\ IF lo < hi
          THEN /\ mid' = (lo + hi) \div 2
               /\ pc' = "ms1a"
          ELSE /\ pc' = "ret"
               /\ UNCHANGED mid
    /\ UNCHANGED << a, b, stack, lo, hi, i, j, k >>

ms1a ==
    /\ pc = "ms1a"
    /\ lo' = lo
    /\ hi' = mid
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "ms2",
                     lo        |-> lo,
                     hi        |-> hi,
                     mid       |-> mid,
                     i         |-> i,
                     j         |-> j,
                     k         |-> k ] >> \o stack
    /\ mid' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

ms2 ==
    /\ pc = "ms2"
    /\ lo' = mid + 1
    /\ hi' = hi
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "ms3",
                     lo        |-> lo,
                     hi        |-> hi,
                     mid       |-> mid,
                     i         |-> i,
                     j         |-> j,
                     k         |-> k ] >> \o stack
    /\ mid' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

ms3 ==
    /\ pc = "ms3"
    /\ i' = lo
    /\ j' = mid + 1
    /\ k' = lo
    /\ pc' = "ms4"
    /\ UNCHANGED << a, b, stack, lo, hi, mid >>

MergeStep ==
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
          ELSE /\ pc' = "ms5"
               /\ UNCHANGED << b, i, j, k >>
    /\ UNCHANGED << a, stack, lo, hi, mid >>

ms4 == MergeStep

ms5 ==
    /\ pc = "ms5"
    /\ k' = lo
    /\ pc' = "ms6"
    /\ UNCHANGED << a, b, stack, lo, hi, mid, i, j >>

ms6 ==
    /\ pc = "ms6"
    /\ IF k <= hi
          THEN /\ a' = [a EXCEPT ![k] = b[k]]
               /\ k' = k + 1
               /\ pc' = "ms6"
          ELSE /\ pc' = "ret"
               /\ UNCHANGED << a, k >>
    /\ UNCHANGED << b, stack, lo, hi, mid, i, j >>

ret ==
    /\ pc = "ret"
    /\ pc' = Head(stack).pc
    /\ lo' = Head(stack).lo
    /\ hi' = Head(stack).hi
    /\ mid' = Head(stack).mid
    /\ i' = Head(stack).i
    /\ j' = Head(stack).j
    /\ k' = Head(stack).k
    /\ stack' = Tail(stack)
    /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms1a \/ ms2 \/ ms3 \/ ms4 \/ ms5 \/ ms6 \/ ret

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ lo' = 1
    /\ hi' = Len(a)
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "Done",
                     lo        |-> lo,
                     hi        |-> hi,
                     mid       |-> mid,
                     i         |-> i,
                     j         |-> j,
                     k         |-> k ] >> \o stack
    /\ mid' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == mergesort \/ Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

Sorted == \A p, q \in 1..Len(a) : p < q => a[p] <= a[q]

Invariant == (pc = "Done") => Sorted

PossibleCounts == Len(a) \in 0..ArrayLen /\ Len(b) = Len(a)

_POSSIBLE == PossibleCounts

=============================================================================
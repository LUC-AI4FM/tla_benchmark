------------------------------ MODULE MergeSort ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

\* TLC registers used as coverage counters for the POSTCONDITION
\* 1: number of observed states in which sorting is complete
\* 2: number of observed merge-step transitions
ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

(***************************************************************************
--algorithm MergeSort {
  variables a \in UNION {[1..N -> 1..N] : N \in 0..ArrayLen},
            b = a;

  procedure mergesort(l, r)
    variables i, j, k, m;
  {
   ms1: if (r > l) {
          m := (l + r) \div 2;
          call mergesort(l, m);
   ms2:   call mergesort(m + 1, r);
   ms3:   i := m + 1;
   cp1:   while (i > l) { b[i-1] := a[i-1]; i := i - 1 };
          j := m;
   cp2:   while (j < r) { b[r+m-j] := a[j+1]; j := j + 1 };
          k := l;
   mg:    while (k <= r) {
            if (b[i] < b[j]) { a[k] := b[i]; i := i + 1 }
            else             { a[k] := b[j]; j := j - 1 };
            k := k + 1
          }
        };
   ret: return
  }

  {
   main: call mergesort(1, Len(a))
  }
}
 ***************************************************************************)

CONSTANT defaultInitValue

VARIABLES a, b, pc, stack, l, r, i, j, k, m

vars == << a, b, pc, stack, l, r, i, j, k, m >>

Init ==
    /\ a \in UNION {[1..N -> 1..N] : N \in 0..ArrayLen}
    /\ b = a
    /\ l = defaultInitValue
    /\ r = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue
    /\ m = defaultInitValue
    /\ stack = << >>
    /\ pc = "main"

ms1 ==
    /\ pc = "ms1"
    /\ IF r > l
         THEN LET mid == (l + r) \div 2 IN
              /\ m' = defaultInitValue
              /\ stack' = << [ procedure |-> "mergesort",
                               pc        |-> "ms2",
                               i         |-> i,
                               j         |-> j,
                               k         |-> k,
                               m         |-> mid,
                               l         |-> l,
                               r         |-> r ] >> \o stack
              /\ l' = l
              /\ r' = mid
              /\ i' = defaultInitValue
              /\ j' = defaultInitValue
              /\ k' = defaultInitValue
              /\ pc' = "ms1"
         ELSE /\ pc' = "ret"
              /\ UNCHANGED << stack, l, r, i, j, k, m >>
    /\ UNCHANGED << a, b >>

ms2 ==
    /\ pc = "ms2"
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "ms3",
                     i         |-> i,
                     j         |-> j,
                     k         |-> k,
                     m         |-> m,
                     l         |-> l,
                     r         |-> r ] >> \o stack
    /\ l' = m + 1
    /\ r' = r
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ m' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

ms3 ==
    /\ pc = "ms3"
    /\ i' = m + 1
    /\ pc' = "cp1"
    /\ UNCHANGED << a, b, stack, l, r, j, k, m >>

cp1 ==
    /\ pc = "cp1"
    /\ IF i > l
         THEN /\ b' = [b EXCEPT ![i-1] = a[i-1]]
              /\ i' = i - 1
              /\ pc' = "cp1"
              /\ UNCHANGED j
         ELSE /\ j' = m
              /\ pc' = "cp2"
              /\ UNCHANGED << b, i >>
    /\ UNCHANGED << a, stack, l, r, k, m >>

cp2 ==
    /\ pc = "cp2"
    /\ IF j < r
         THEN /\ b' = [b EXCEPT ![r+m-j] = a[j+1]]
              /\ j' = j + 1
              /\ pc' = "cp2"
              /\ UNCHANGED k
         ELSE /\ k' = l
              /\ pc' = "mg"
              /\ UNCHANGED << b, j >>
    /\ UNCHANGED << a, stack, l, r, i, m >>

mg ==
    /\ pc = "mg"
    /\ IF k <= r
         THEN /\ IF b[i] < b[j]
                   THEN /\ a' = [a EXCEPT ![k] = b[i]]
                        /\ i' = i + 1
                        /\ UNCHANGED j
                   ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                        /\ j' = j - 1
                        /\ UNCHANGED i
              /\ k' = k + 1
              /\ pc' = "mg"
              /\ TLCSet(2, TLCGet(2) + 1)
         ELSE /\ pc' = "ret"
              /\ UNCHANGED << a, i, j, k >>
    /\ UNCHANGED << b, stack, l, r, m >>

ret ==
    /\ pc = "ret"
    /\ pc' = Head(stack).pc
    /\ i' = Head(stack).i
    /\ j' = Head(stack).j
    /\ k' = Head(stack).k
    /\ m' = Head(stack).m
    /\ l' = Head(stack).l
    /\ r' = Head(stack).r
    /\ stack' = Tail(stack)
    /\ IF Head(stack).pc = "Done" THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms2 \/ ms3 \/ cp1 \/ cp2 \/ mg \/ ret

main ==
    /\ pc = "main"
    /\ l' = 1
    /\ r' = Len(a)
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "Done",
                     i         |-> i,
                     j         |-> j,
                     k         |-> k,
                     m         |-> m,
                     l         |-> l,
                     r         |-> r ] >> \o stack
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ m' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == main \/ mergesort \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

Sorted(f) == \A x, y \in DOMAIN f : x < y => f[x] <= f[y]

Invariant == pc = "Done" => Sorted(a)

\* Checked as a POSTCONDITION after model checking with ArrayLen = 2.
PossibleCounts ==
    /\ TLCGet(1) = 12
    /\ TLCGet(2) = 8

=============================================================================
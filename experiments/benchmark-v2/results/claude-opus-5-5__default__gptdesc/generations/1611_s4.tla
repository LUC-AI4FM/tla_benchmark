------------------------------ MODULE MergeSort ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS N, ArrayLen, defaultInitValue

ASSUME /\ N \in Nat \ {0}
       /\ ArrayLen \in Nat

ArrayVals == UNION { [1..len -> 1..N] : len \in 0..ArrayLen }

(***************************************************************************
--algorithm MergeSort {
  variables a \in ArrayVals, b = a ;

  procedure mergesort(lo, hi)
    variables med, i, j, k ;
  {
    ms1: if (lo < hi) {
           med := (lo + hi) \div 2 ;
    ms2:   call mergesort(lo, med) ;
    ms3:   call mergesort(med + 1, hi) ;
    ms4:   i := lo ; j := med + 1 ; k := lo ;
    ms5:   while (k <= hi) {
             if (j > hi \/ (i <= med /\ a[i] <= a[j])) {
               b[k] := a[i] ; i := i + 1
             } else {
               b[k] := a[j] ; j := j + 1
             } ;
             k := k + 1
           } ;
    ms6:   k := lo ;
    ms7:   while (k <= hi) {
             a[k] := b[k] ; k := k + 1
           }
         } ;
    ms8: return
  }

  {
    main: call mergesort(1, Len(a))
  }
}
 ***************************************************************************)

VARIABLES a, b, pc, stack, lo, hi, med, i, j, k

vars == << a, b, pc, stack, lo, hi, med, i, j, k >>

Init == /\ a \in ArrayVals
        /\ b = a
        /\ lo = defaultInitValue
        /\ hi = defaultInitValue
        /\ med = defaultInitValue
        /\ i = defaultInitValue
        /\ j = defaultInitValue
        /\ k = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

ms1 == /\ pc = "ms1"
       /\ IF lo < hi
             THEN /\ med' = (lo + hi) \div 2
                  /\ pc' = "ms2"
             ELSE /\ pc' = "ms8"
                  /\ med' = med
       /\ UNCHANGED << a, b, stack, lo, hi, i, j, k >>

ms2 == /\ pc = "ms2"
       /\ lo' = lo
       /\ hi' = med
       /\ stack' = << [ procedure |-> "mergesort",
                        pc        |-> "ms3",
                        med       |-> med,
                        i         |-> i,
                        j         |-> j,
                        k         |-> k,
                        lo        |-> lo,
                        hi        |-> hi ] >> \o stack
       /\ med' = defaultInitValue
       /\ i' = defaultInitValue
       /\ j' = defaultInitValue
       /\ k' = defaultInitValue
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms3 == /\ pc = "ms3"
       /\ lo' = med + 1
       /\ hi' = hi
       /\ stack' = << [ procedure |-> "mergesort",
                        pc        |-> "ms4",
                        med       |-> med,
                        i         |-> i,
                        j         |-> j,
                        k         |-> k,
                        lo        |-> lo,
                        hi        |-> hi ] >> \o stack
       /\ med' = defaultInitValue
       /\ i' = defaultInitValue
       /\ j' = defaultInitValue
       /\ k' = defaultInitValue
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms4 == /\ pc = "ms4"
       /\ i' = lo
       /\ j' = med + 1
       /\ k' = lo
       /\ pc' = "ms5"
       /\ UNCHANGED << a, b, stack, lo, hi, med >>

ms5 == /\ pc = "ms5"
       /\ IF k <= hi
             THEN /\ IF j > hi \/ (i <= med /\ a[i] <= a[j])
                        THEN /\ b' = [b EXCEPT ![k] = a[i]]
                             /\ i' = i + 1
                             /\ j' = j
                        ELSE /\ b' = [b EXCEPT ![k] = a[j]]
                             /\ j' = j + 1
                             /\ i' = i
                  /\ k' = k + 1
                  /\ pc' = "ms5"
             ELSE /\ pc' = "ms6"
                  /\ UNCHANGED << b, i, j, k >>
       /\ UNCHANGED << a, stack, lo, hi, med >>

ms6 == /\ pc = "ms6"
       /\ k' = lo
       /\ pc' = "ms7"
       /\ UNCHANGED << a, b, stack, lo, hi, med, i, j >>

ms7 == /\ pc = "ms7"
       /\ IF k <= hi
             THEN /\ a' = [a EXCEPT ![k] = b[k]]
                  /\ k' = k + 1
                  /\ pc' = "ms7"
             ELSE /\ pc' = "ms8"
                  /\ UNCHANGED << a, k >>
       /\ UNCHANGED << b, stack, lo, hi, med, i, j >>

ms8 == /\ pc = "ms8"
       /\ pc' = Head(stack).pc
       /\ med' = Head(stack).med
       /\ i' = Head(stack).i
       /\ j' = Head(stack).j
       /\ k' = Head(stack).k
       /\ lo' = Head(stack).lo
       /\ hi' = Head(stack).hi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms2 \/ ms3 \/ ms4 \/ ms5 \/ ms6 \/ ms7 \/ ms8

main == /\ pc = "main"
        /\ lo' = 1
        /\ hi' = Len(a)
        /\ stack' = << [ procedure |-> "mergesort",
                         pc        |-> "Done",
                         med       |-> med,
                         i         |-> i,
                         j         |-> j,
                         k         |-> k,
                         lo        |-> lo,
                         hi        |-> hi ] >> \o stack
        /\ med' = defaultInitValue
        /\ i' = defaultInitValue
        /\ j' = defaultInitValue
        /\ k' = defaultInitValue
        /\ pc' = "ms1"
        /\ UNCHANGED << a, b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == main \/ mergesort \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Safety: when the algorithm is done, the array is sorted. *)

IsSorted(s) == \A x, y \in 1..Len(s) : x < y => s[x] <= s[y]

Sorted == (pc = "Done") => IsSorted(a)

TypeOK == /\ a \in ArrayVals
          /\ b \in ArrayVals
          /\ DOMAIN b = DOMAIN a

=============================================================================
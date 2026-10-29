------------------------------ MODULE MergeSort ------------------------------
(***************************************************************************)
(* A recursive mergesort algorithm, written as a PlusCal procedure and     *)
(* translated by hand into TLA+.  The array a is a sequence of values in   *)
(* 1..N, of any length from 0 to ArrayLen.  The procedure uses an          *)
(* auxiliary buffer b for merging and an explicit call stack to model the  *)
(* recursive procedure calls.                                              *)
(*                                                                         *)
(* --algorithm MergeSort {                                                 *)
(*   variables a \in UNION {[1..n -> 1..N] : n \in 0..ArrayLen},           *)
(*             b = a, i = 0, j = 0, k = 0;                                 *)
(*   procedure mergesort(lo = 0, hi = 0)                                   *)
(*     variable med = 0; {                                                 *)
(*     ms1: if (lo < hi) { med := (lo + hi) \div 2;                        *)
(*                         call mergesort(lo, med) }                       *)
(*          else return;                                                   *)
(*     ms2: call mergesort(med + 1, hi);                                   *)
(*     ms3: i := lo; j := med + 1; k := lo;                                *)
(*     ms4: while (k <= hi) {                                              *)
(*            if (i <= med /\ (j > hi \/ a[i] <= a[j]))                    *)
(*                 { b[k] := a[i]; i := i + 1 }                            *)
(*            else { b[k] := a[j]; j := j + 1 };                           *)
(*            k := k + 1 };                                                *)
(*          k := lo;                                                       *)
(*     ms5: while (k <= hi) { a[k] := b[k]; k := k + 1 };                  *)
(*          return }                                                       *)
(*   { main: call mergesort(1, Len(a)) }                                   *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS N, ArrayLen

ASSUME N \in Nat \ {0}
ASSUME ArrayLen \in Nat

VARIABLES a, b, i, j, k, pc, stack, lo, hi, med

vars == <<a, b, i, j, k, pc, stack, lo, hi, med>>

PossibleArrays == UNION {[1..n -> 1..N] : n \in 0..ArrayLen}

Init ==
  /\ a \in PossibleArrays
  /\ b = a
  /\ i = 0
  /\ j = 0
  /\ k = 0
  /\ lo = 0
  /\ hi = 0
  /\ med = 0
  /\ stack = << >>
  /\ pc = "main"

\* Pushing a frame for a call of mergesort that returns to label ret.
Frame(ret) == [procedure |-> "mergesort", pc |-> ret,
               lo |-> lo, hi |-> hi, med |-> med]

\* Returning from mergesort: restore caller's locals and pc.
Return ==
  /\ pc'    = Head(stack).pc
  /\ lo'    = Head(stack).lo
  /\ hi'    = Head(stack).hi
  /\ med'   = Head(stack).med
  /\ stack' = Tail(stack)

main ==
  /\ pc = "main"
  /\ stack' = << Frame("Done") >> \o stack
  /\ lo' = 1
  /\ hi' = Len(a)
  /\ med' = 0
  /\ pc' = "ms1"
  /\ UNCHANGED <<a, b, i, j, k>>

ms1 ==
  /\ pc = "ms1"
  /\ IF lo < hi
       THEN LET m == (lo + hi) \div 2 IN
              /\ stack' = << [procedure |-> "mergesort", pc |-> "ms2",
                              lo |-> lo, hi |-> hi, med |-> m] >> \o stack
              /\ lo' = lo
              /\ hi' = m
              /\ med' = 0
              /\ pc' = "ms1"
       ELSE Return
  /\ UNCHANGED <<a, b, i, j, k>>

ms2 ==
  /\ pc = "ms2"
  /\ stack' = << Frame("ms3") >> \o stack
  /\ lo' = med + 1
  /\ hi' = hi
  /\ med' = 0
  /\ pc' = "ms1"
  /\ UNCHANGED <<a, b, i, j, k>>

ms3 ==
  /\ pc = "ms3"
  /\ i' = lo
  /\ j' = med + 1
  /\ k' = lo
  /\ pc' = "ms4"
  /\ UNCHANGED <<a, b, stack, lo, hi, med>>

ms4 ==
  /\ pc = "ms4"
  /\ IF k <= hi
       THEN /\ IF i <= med /\ (j > hi \/ a[i] <= a[j])
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
            /\ UNCHANGED <<b, i, j>>
  /\ UNCHANGED <<a, stack, lo, hi, med>>

ms5 ==
  /\ pc = "ms5"
  /\ IF k <= hi
       THEN /\ a' = [a EXCEPT ![k] = b[k]]
            /\ k' = k + 1
            /\ pc' = "ms5"
            /\ UNCHANGED <<stack, lo, hi, med>>
       ELSE /\ Return
            /\ UNCHANGED <<a, k>>
  /\ UNCHANGED <<b, i, j>>

mergesort == ms1 \/ ms2 \/ ms3 \/ ms4 \/ ms5

Terminating == pc = "Done" /\ UNCHANGED vars

Next == main \/ mergesort \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ a \in PossibleArrays
  /\ DOMAIN b = DOMAIN a
  /\ i \in Int /\ j \in Int /\ k \in Int
  /\ lo \in Int /\ hi \in Int /\ med \in Int
  /\ pc \in {"main", "ms1", "ms2", "ms3", "ms4", "ms5", "Done"}

Sorted(s) == \A x, y \in 1..Len(s) : x < y => s[x] <= s[y]

\* Safety: when the algorithm finishes, the array is sorted.
SortedWhenDone == (pc = "Done") => Sorted(a)

\* Liveness: the algorithm terminates.
Termination == <>(pc = "Done")

THEOREM Spec => []TypeOK /\ []SortedWhenDone /\ Termination
=============================================================================
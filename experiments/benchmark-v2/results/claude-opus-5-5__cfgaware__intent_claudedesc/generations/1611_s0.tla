------------------------------- MODULE MergeSort -------------------------------
(***************************************************************************)
(* Merge sort as transcribed from Sedgewick, "Algorithms" (2nd edition),   *)
(* page 166.  The array is split recursively; each half is copied into a   *)
(* temporary buffer b, the second half in mirrored (reversed) order, and   *)
(* the two halves are then merged back from b into a.                      *)
(*                                                                         *)
(*   procedure mergesort(l, r)                                             *)
(*     var i, j, k, m;                                                     *)
(*     if r - l > 0 then                                                   *)
(*       m := (r + l) div 2;                                               *)
(*       mergesort(l, m);                                                  *)
(*       mergesort(m + 1, r);                                              *)
(*       for i := m downto l do b[i] := a[i];                              *)
(*       for j := m + 1 to r do b[r + m + 1 - j] := a[j];                  *)
(*       i := l; j := r;                                                   *)
(*       for k := l to r do                                                *)
(*         if b[i] < b[j] then a[k] := b[i]; i := i + 1                    *)
(*                        else a[k] := b[j]; j := j - 1                    *)
(*                                                                         *)
(* This module is the hand-written translation of the PlusCal algorithm.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS ArrayLen, defaultInitValue

ASSUME ArrayLen \in Nat

(* All arrays of any length between 0 and ArrayLen. *)
Arrays == UNION { [1..N -> 1..N] : N \in 0..ArrayLen }

VARIABLES a, b, pc, stack, l, r, i, j, k, m

vars == << a, b, pc, stack, l, r, i, j, k, m >>

Len_a == Cardinality_helper(a)
Cardinality_helper(f) == IF DOMAIN f = {} THEN 0
                         ELSE CHOOSE n \in 0..ArrayLen : DOMAIN f = 1..n

Init == /\ a \in Arrays
        /\ b = a
        /\ stack = << >>
        /\ l = defaultInitValue
        /\ r = defaultInitValue
        /\ i = defaultInitValue
        /\ j = defaultInitValue
        /\ k = defaultInitValue
        /\ m = defaultInitValue
        /\ pc = "Main"

(* Main: call mergesort(1, Len(a)) *)
Main == /\ pc = "Main"
        /\ stack' = << [ procedure |-> "mergesort",
                         pc        |-> "Done",
                         l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m ] >>
                    \o stack
        /\ l' = 1
        /\ r' = Cardinality_helper(a)
        /\ i' = defaultInitValue
        /\ j' = defaultInitValue
        /\ k' = defaultInitValue
        /\ m' = defaultInitValue
        /\ pc' = "ms1"
        /\ UNCHANGED << a, b >>

ms1 == /\ pc = "ms1"
       /\ IF r - l > 0
            THEN /\ m' = (r + l) \div 2
                 /\ pc' = "ms2"
            ELSE /\ pc' = "ret"
                 /\ m' = m
       /\ UNCHANGED << a, b, stack, l, r, i, j, k >>

(* call mergesort(l, m) *)
ms2 == /\ pc = "ms2"
       /\ stack' = << [ procedure |-> "mergesort",
                        pc        |-> "ms3",
                        l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m ] >>
                   \o stack
       /\ l' = l
       /\ r' = m
       /\ i' = defaultInitValue
       /\ j' = defaultInitValue
       /\ k' = defaultInitValue
       /\ m' = defaultInitValue
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

(* call mergesort(m + 1, r) *)
ms3 == /\ pc = "ms3"
       /\ stack' = << [ procedure |-> "mergesort",
                        pc        |-> "ms4",
                        l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m ] >>
                   \o stack
       /\ l' = m + 1
       /\ r' = r
       /\ i' = defaultInitValue
       /\ j' = defaultInitValue
       /\ k' = defaultInitValue
       /\ m' = defaultInitValue
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms4 == /\ pc = "ms4"
       /\ i' = m
       /\ pc' = "copy1"
       /\ UNCHANGED << a, b, stack, l, r, j, k, m >>

(* for i := m downto l do b[i] := a[i] *)
copy1 == /\ pc = "copy1"
         /\ IF i >= l
              THEN /\ b' = [b EXCEPT ![i] = a[i]]
                   /\ i' = i - 1
                   /\ j' = j
                   /\ pc' = "copy1"
              ELSE /\ b' = b
                   /\ i' = i
                   /\ j' = m + 1
                   /\ pc' = "copy2"
         /\ UNCHANGED << a, stack, l, r, k, m >>

(* for j := m + 1 to r do b[r + m + 1 - j] := a[j] *)
copy2 == /\ pc = "copy2"
         /\ IF j <= r
              THEN /\ b' = [b EXCEPT ![r + m + 1 - j] = a[j]]
                   /\ j' = j + 1
                   /\ i' = i
                   /\ k' = k
                   /\ pc' = "copy2"
              ELSE /\ b' = b
                   /\ i' = l
                   /\ j' = r
                   /\ k' = l
                   /\ pc' = "merge"
         /\ UNCHANGED << a, stack, l, r, m >>

(* for k := l to r do if b[i] < b[j] then ... else ... *)
merge == /\ pc = "merge"
         /\ IF k <= r
              THEN /\ IF b[i] < b[j]
                        THEN /\ a' = [a EXCEPT ![k] = b[i]]
                             /\ i' = i + 1
                             /\ j' = j
                        ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                             /\ j' = j - 1
                             /\ i' = i
                   /\ k' = k + 1
                   /\ pc' = "merge"
              ELSE /\ UNCHANGED << a, i, j, k >>
                   /\ pc' = "ret"
         /\ UNCHANGED << b, stack, l, r, m >>

(* return *)
ret == /\ pc = "ret"
       /\ pc' = Head(stack).pc
       /\ l' = Head(stack).l
       /\ r' = Head(stack).r
       /\ i' = Head(stack).i
       /\ j' = Head(stack).j
       /\ k' = Head(stack).k
       /\ m' = Head(stack).m
       /\ stack' = Tail(stack)
       /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms2 \/ ms3 \/ ms4 \/ copy1 \/ copy2 \/ merge \/ ret

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Main \/ mergesort \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

IsSorted(arr) == \A x, y \in DOMAIN arr : x < y => arr[x] <= arr[y]

Invariant == pc = "Done" => IsSorted(a)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Labels used for counting reachable states / transitions. *)

(* States satisfying the "sorted" termination condition. *)
Sorted == pc = "Done" /\ IsSorted(a)

(* A merge-step transition: one iteration of the merge loop. *)
MergeStep == merge

(* Expected counts for ArrayLen = 2. *)
PossibleCounts == [ Sorted |-> 6, MergeStep |-> 8 ]

_POSSIBLE == /\ PossibleCounts.Sorted \in Nat
             /\ PossibleCounts.MergeStep \in Nat

=============================================================================
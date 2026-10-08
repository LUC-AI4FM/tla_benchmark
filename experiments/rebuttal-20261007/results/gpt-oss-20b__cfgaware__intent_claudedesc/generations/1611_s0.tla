------------------------------ MODULE MergeSort ------------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS ArrayLen
defaultInitValue == 0

VARIABLES arr, len, width, i, state

(* ------------------------------------------------------------------ *)
(* Helper definitions *)

SubSeq(arr, start, end) ==
  IF start > end THEN <<>> ELSE [arr[j] : j \in start..end]

MergeSorted(l, r) ==
  IF l = <<>> THEN r
  ELSE IF r = <<>> THEN l
  ELSE IF FIRST l <= FIRST r THEN <<FIRST l>> ^ MergeSorted(TAIL l, r)
       ELSE <<FIRST r>> ^ MergeSorted(l, TAIL r)

UpdateArr(arr, s, seq) ==
  [j \in 1..len |-> 
      IF j >= s /\ j < s + Len(seq) THEN seq[j - s + 1] ELSE arr[j]]

(* ------------------------------------------------------------------ *)
(* Sortedness predicate *)

Sorted(a) == 
  ∀ x,y \in DOMAIN a : x < y => a[x] <= a[y]

Termination == state = "done"

Invariant == Termination => Sorted(arr)

(* ------------------------------------------------------------------ *)
(* Initial condition *)

Init ==
  /\ len \in 0..ArrayLen
  /\ arr \in [1..len -> Nat]
  /\ width = 1
  /\ i = 0
  /\ state = "merging"

(* ------------------------------------------------------------------ *)
(* Next-state relation *)

Next ==
  \/ (state = "merging" /\ i < len) =>
        LET mergedSeq == MergeSorted(SubSeq(arr, i, Min(i+width-1,len)),
                                     SubSeq(arr, i+width, Min(i+2*width-1,len))) IN
           /\ arr'   = UpdateArr(arr, i, mergedSeq)
           /\ i'     = i + 2*width
           /\ width' = width
           /\ state' = "merging"
           /\ len'   = len
  \/ (state = "merging" /\ i >= len) =>
        LET newWidth == 2*width IN
           IF newWidth > len THEN
              /\ arr'   = arr
              /\ i'     = 0
              /\ width' = newWidth
              /\ state' = "done"
              /\ len'   = len
           ELSE
              /\ arr'   = arr
              /\ i'     = 0
              /\ width' = newWidth
              /\ state' = "merging"
              /\ len'   = len
  \/ (state = "done") => UNCHANGED <<arr, len, width, i, state>>

(* ------------------------------------------------------------------ *)
(* Specification *)

Spec == Init /\ [][Next]_<<arr, len, width, i, state>>

=============================================================================
------------------------------ MODULE MergeSort ------------------------------
(***************************************************************************)
(* A formal model of mergesort over a fixed-length array of integers.      *)
(*                                                                         *)
(* Recursion is modeled with an explicit stack of frames [lo, hi, phase].  *)
(*   phase 0 : the left half [lo..mid] still has to be sorted              *)
(*   phase 1 : the right half [mid+1..hi] still has to be sorted           *)
(*   phase 2 : both halves are sorted, so merge them                       *)
(*                                                                         *)
(* Merging copies elements one at a time into the temporary sequence tmp.  *)
(* It then copies tmp back into the array, one write per step.             *)
(* The array is changed only through the Read and Write operators.         *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS ArrayLen, defaultInitValue

ASSUME ArrayLen \in Nat

\* The finite set of integer values an array element may initially hold.
Values == 1..ArrayLen

Indices == 1..ArrayLen

VARIABLES
    A,      \* the array being sorted
    A0,     \* the initial contents of the array (ghost variable)
    pc,     \* control location: "sort", "merge", "copy" or "Done"
    stack,  \* recursion stack of frames [lo, hi, phase]
    tmp,    \* local temporary storage used for merging
    mlo, mmid, mhi,  \* bounds of the current merge
    i, j,   \* read cursors into the left and right halves
    k       \* write cursor used when copying tmp back into A

vars == <<A, A0, pc, stack, tmp, mlo, mmid, mhi, i, j, k>>

-----------------------------------------------------------------------------
(* Well-specified read and write operations on array indices *)
Read(arr, idx) == arr[idx]
Write(arr, idx, v) == [arr EXCEPT ![idx] = v]

(* Helper operators for reasoning about sequences and multisets *)
Range(s) == {s[x] : x \in DOMAIN s}

Count(s, v) == Cardinality({x \in DOMAIN s : s[x] = v})

IsSorted(s) == \A p, q \in DOMAIN s : p < q => s[p] <= s[q]

IsPerm(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A v \in Range(s) \cup Range(t) : Count(s, v) = Count(t, v)

Seg(arr, lo, hi) == IF lo > hi THEN << >> ELSE SubSeq(arr, lo, hi)

Mid(f) == (f.lo + f.hi) \div 2

-----------------------------------------------------------------------------
Init ==
    /\ A \in [Indices -> Values]
    /\ A0 = A
    /\ pc = "sort"
    /\ stack = << [lo |-> 1, hi |-> ArrayLen, phase |-> 0] >>
    /\ tmp = << >>
    /\ mlo = defaultInitValue
    /\ mmid = defaultInitValue
    /\ mhi = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue

(* Divide-and-conquer control: split a frame, recurse, or start a merge *)
SortStep ==
    /\ pc = "sort"
    /\ IF stack = << >>
         THEN /\ pc' = "Done"
              /\ UNCHANGED <<A, A0, stack, tmp, mlo, mmid, mhi, i, j, k>>
         ELSE LET f == stack[Len(stack)] IN
              IF f.hi - f.lo < 1
                THEN \* A subarray of size 0 or 1 is already sorted: return.
                     /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
                     /\ UNCHANGED <<A, A0, pc, tmp, mlo, mmid, mhi, i, j, k>>
              ELSE IF f.phase = 0
                THEN \* Recursive call on the left half.
                     /\ stack' = Append([stack EXCEPT ![Len(stack)].phase = 1],
                                        [lo |-> f.lo, hi |-> Mid(f), phase |-> 0])
                     /\ UNCHANGED <<A, A0, pc, tmp, mlo, mmid, mhi, i, j, k>>
              ELSE IF f.phase = 1
                THEN \* Recursive call on the right half.
                     /\ stack' = Append([stack EXCEPT ![Len(stack)].phase = 2],
                                        [lo |-> Mid(f) + 1, hi |-> f.hi, phase |-> 0])
                     /\ UNCHANGED <<A, A0, pc, tmp, mlo, mmid, mhi, i, j, k>>
              ELSE \* Both halves are sorted: start merging, then return.
                     /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
                     /\ mlo' = f.lo
                     /\ mmid' = Mid(f)
                     /\ mhi' = f.hi
                     /\ i' = f.lo
                     /\ j' = Mid(f) + 1
                     /\ tmp' = << >>
                     /\ pc' = "merge"
                     /\ UNCHANGED <<A, A0, k>>

(* Merge phase: move one element from the two sorted halves into tmp *)
MergeAction ==
    /\ pc = "merge"
    /\ IF i <= mmid /\ (j > mhi \/ Read(A, i) <= Read(A, j))
         THEN /\ tmp' = Append(tmp, Read(A, i))
              /\ i' = i + 1
              /\ UNCHANGED <<j, pc, k>>
       ELSE IF j <= mhi
         THEN /\ tmp' = Append(tmp, Read(A, j))
              /\ j' = j + 1
              /\ UNCHANGED <<i, pc, k>>
       ELSE /\ pc' = "copy"
            /\ k' = mlo
            /\ UNCHANGED <<tmp, i, j>>
    /\ UNCHANGED <<A, A0, stack, mlo, mmid, mhi>>

(* Copy phase: write tmp back into A[mlo..mhi], one index per step *)
CopyAction ==
    /\ pc = "copy"
    /\ IF k <= mhi
         THEN /\ A' = Write(A, k, tmp[k - mlo + 1])
              /\ k' = k + 1
              /\ UNCHANGED pc
         ELSE /\ pc' = "sort"
              /\ UNCHANGED <<A, k>>
    /\ UNCHANGED <<A0, stack, tmp, mlo, mmid, mhi, i, j>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == SortStep \/ MergeAction \/ CopyAction \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

TypeOK ==
    /\ A \in [Indices -> Values]
    /\ A0 \in [Indices -> Values]
    /\ pc \in {"sort", "merge", "copy", "Done"}
    /\ tmp \in Seq(Values)

\* Safety: once the algorithm terminates, the array is nondecreasing.
Sorted ==
    pc = "Done" => \A p, q \in Indices : p < q => A[p] <= A[q]

\* Preservation: the final multiset of elements equals the initial one.
\* Outside the copy phase, A is always a permutation of A0.
PossibleCounts ==
    /\ pc \in {"sort", "merge", "Done"} => IsPerm(A, A0)
    /\ pc = "Done" => \A v \in Values : Count(A, v) = Count(A0, v)

\* Correctness of the merging step.
MergeStep ==
    /\ pc = "merge" =>
         /\ IsSorted(Seg(A, mlo, mmid))
         /\ IsSorted(Seg(A, mmid + 1, mhi))
         /\ IsSorted(tmp)
         /\ IsPerm(tmp, Seg(A, mlo, i - 1) \o Seg(A, mmid + 1, j - 1))
    /\ pc = "copy" =>
         /\ Len(tmp) = mhi - mlo + 1
         /\ IsSorted(tmp)
         /\ \A x \in mlo..(k - 1) : A[x] = tmp[x - mlo + 1]

\* Sanity bound: every value occurs between 0 and ArrayLen times.
_POSSIBLE ==
    \A v \in Values : Count(A, v) \in 0..ArrayLen

Invariant == TypeOK /\ Sorted /\ PossibleCounts /\ MergeStep /\ _POSSIBLE

\* Liveness: the algorithm eventually terminates.
Termination == <>(pc = "Done")

=============================================================================
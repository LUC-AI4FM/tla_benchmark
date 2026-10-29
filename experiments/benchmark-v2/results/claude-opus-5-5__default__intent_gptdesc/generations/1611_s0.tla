------------------------------- MODULE MergeSort -------------------------------
(***************************************************************************)
(* An abstract model of mergesort on an integer array of length N.        *)
(*                                                                         *)
(* The divide-and-conquer recursion is modelled by an explicit work stack  *)
(* of frames. Each frame is [lo, hi, ph]:                                  *)
(*   ph = "split" : sort the subarray arr[lo..hi].                         *)
(*   ph = "merge" : both halves of arr[lo..hi] are sorted; merge them.     *)
(* A "split" frame for a subarray of length > 1 is replaced by a pending   *)
(* "merge" frame and two recursive "split" frames for the halves. This is  *)
(* equivalent to recursive calls, and it also covers iterative             *)
(* stack-based implementations.                                            *)
(*                                                                         *)
(* Merging uses local temporary storage (buf). The merge reads arr one     *)
(* index at a time and appends the smaller head element to buf. It then    *)
(* copies buf back into arr[lo..hi] one index write at a time. Every       *)
(* update to arr is a single-index write: arr' = [arr EXCEPT ![idx] = v].  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N,        \* length of the array
    Values    \* finite set of integers the elements are drawn from

ASSUME NAssump      == N \in Nat
ASSUME ValuesAssump == Values \subseteq Int /\ IsFiniteSet(Values) /\ Values # {}

VARIABLES
    arr,     \* the array being sorted (a function 1..N -> Values)
    arr0,    \* ghost copy of the initial array, used for the permutation property
    stack,   \* work stack of frames (Head = top)
    m,       \* state of the merge currently in progress (local storage)
    pc       \* "Running" or "Done"

vars == <<arr, arr0, stack, m, pc>>

Idx == 1..N

-----------------------------------------------------------------------------
(* Helper operators                                                       *)

Range(s) == { s[i] : i \in DOMAIN s }

IsSorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Multiset view of a sequence: number of occurrences of v.
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

\* s and t are equal as multisets.
IsPerm(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A v \in Range(s) \cup Range(t) : Count(s, v) = Count(t, v)

\* Correctness condition for the merge step:
\* r is a sorted arrangement of the concatenation a \o b.
IsMergeOf(r, a, b) == IsSorted(r) /\ IsPerm(r, a \o b)

Mid(lo, hi) == (lo + hi) \div 2

Seg(s, lo, hi) == SubSeq(s, lo, hi)

Frame(lo, hi, ph) == [lo |-> lo, hi |-> hi, ph |-> ph]

Idle == [act |-> "idle", lo |-> 0, mid |-> 0, hi |-> 0,
         i |-> 0, j |-> 0, k |-> 0, buf |-> << >>, orig |-> << >>]

Size(r) == r.hi - r.lo + 1

-----------------------------------------------------------------------------
(* Type invariant                                                         *)

FrameType == [lo : Idx, hi : Idx, ph : {"split", "merge"}]

TypeOK ==
    /\ arr  \in [Idx -> Values]
    /\ arr0 \in [Idx -> Values]
    /\ stack \in Seq(FrameType)
    /\ m.act \in {"idle", "merge", "copy"}
    /\ m.buf \in Seq(Values)
    /\ m.orig \in Seq(Values)
    /\ pc \in {"Running", "Done"}

-----------------------------------------------------------------------------
(* Initial state: any contents of the array are allowed.                   *)

Init ==
    /\ arr \in [Idx -> Values]
    /\ arr0 = arr
    /\ stack = IF N > 0 THEN << Frame(1, N, "split") >> ELSE << >>
    /\ m = Idle
    /\ pc = "Running"

-----------------------------------------------------------------------------
(* Divide: split the top subarray or finish a trivial one.                 *)
Split ==
    /\ pc = "Running"
    /\ m.act = "idle"
    /\ stack # << >>
    /\ Head(stack).ph = "split"
    /\ LET f == Head(stack) IN
         IF f.lo >= f.hi
           THEN stack' = Tail(stack)          \* length <= 1: already sorted
           ELSE stack' = << Frame(f.lo, Mid(f.lo, f.hi), "split"),
                            Frame(Mid(f.lo, f.hi) + 1, f.hi, "split"),
                            Frame(f.lo, f.hi, "merge") >> \o Tail(stack)
    /\ UNCHANGED <<arr, arr0, m, pc>>

(* Conquer: begin merging the two sorted halves of the top frame.          *)
BeginMerge ==
    /\ pc = "Running"
    /\ m.act = "idle"
    /\ stack # << >>
    /\ Head(stack).ph = "merge"
    /\ LET f == Head(stack)
           md == Mid(f.lo, f.hi)
       IN m' = [act |-> "merge", lo |-> f.lo, mid |-> md, hi |-> f.hi,
                i |-> f.lo, j |-> md + 1, k |-> 0,
                buf |-> << >>, orig |-> Seg(arr, f.lo, f.hi)]
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<arr, arr0, pc>>

(* One merge step reads arr[i] and/or arr[j] and appends the smaller to buf. *)
MergeStep ==
    /\ pc = "Running"
    /\ m.act = "merge"
    /\ Len(m.buf) < Size(m)
    /\ IF m.i <= m.mid /\ (m.j > m.hi \/ arr[m.i] <= arr[m.j])
         THEN m' = [m EXCEPT !.buf = Append(m.buf, arr[m.i]), !.i = m.i + 1]
         ELSE m' = [m EXCEPT !.buf = Append(m.buf, arr[m.j]), !.j = m.j + 1]
    /\ UNCHANGED <<arr, arr0, stack, pc>>

(* The temporary buffer is full: switch to copy-back.                      *)
MergeDone ==
    /\ pc = "Running"
    /\ m.act = "merge"
    /\ Len(m.buf) = Size(m)
    /\ m' = [m EXCEPT !.act = "copy", !.k = 0]
    /\ UNCHANGED <<arr, arr0, stack, pc>>

(* Copy back: write one array index per step.                              *)
CopyStep ==
    /\ pc = "Running"
    /\ m.act = "copy"
    /\ m.k < Size(m)
    /\ arr' = [arr EXCEPT ![m.lo + m.k] = m.buf[m.k + 1]]
    /\ m' = [m EXCEPT !.k = m.k + 1]
    /\ UNCHANGED <<arr0, stack, pc>>

CopyDone ==
    /\ pc = "Running"
    /\ m.act = "copy"
    /\ m.k = Size(m)
    /\ m' = Idle
    /\ UNCHANGED <<arr, arr0, stack, pc>>

(* Termination: no work remains.                                           *)
Finish ==
    /\ pc = "Running"
    /\ stack = << >>
    /\ m.act = "idle"
    /\ pc' = "Done"
    /\ UNCHANGED <<arr, arr0, stack, m>>

(* Explicit terminal stuttering, so that a finished run is not a deadlock. *)
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Step == Split \/ BeginMerge \/ MergeStep \/ MergeDone
          \/ CopyStep \/ CopyDone \/ Finish

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* Sortedness at termination.
Sortedness == pc = "Done" => IsSorted(arr)

\* Permutation at termination.
Preservation == pc = "Done" => IsPerm(arr, arr0)

\* Stronger inductive-style invariant: the multiset is preserved at all times.
\* During copy-back, the unwritten part of the segment is accounted for by buf.
PermutationInvariant ==
    IF m.act = "copy"
      THEN IsPerm([x \in Idx |-> IF x \in m.lo..m.hi
                                   THEN m.buf[x - m.lo + 1]
                                   ELSE arr[x]], arr0)
      ELSE IsPerm(arr, arr0)

\* Merge precondition: both halves are sorted when merging begins and while it runs.
MergePrecondition ==
    m.act = "merge" =>
        /\ IsSorted(Seg(arr, m.lo, m.mid))
        /\ IsSorted(Seg(arr, m.mid + 1, m.hi))
        /\ Seg(arr, m.lo, m.hi) = m.orig

\* Merge postcondition: the buffer is always sorted. When the buffer is full,
\* it is a sorted merge of the two halves with their combined multiset preserved.
MergeCorrectness ==
    /\ m.act \in {"merge", "copy"} => IsSorted(m.buf)
    /\ m.act = "copy" =>
         IsMergeOf(m.buf,
                   SubSeq(m.orig, 1, m.mid - m.lo + 1),
                   SubSeq(m.orig, m.mid - m.lo + 2, Size(m)))

\* After the copy-back, arr[lo..hi] is the sorted, merged result.
CopyCorrectness ==
    m.act = "copy" =>
        \A x \in m.lo..(m.lo + m.k - 1) : arr[x] = m.buf[x - m.lo + 1]

\* Frames on the stack stay within the array bounds.
StackWellFormed ==
    \A n \in 1..Len(stack) : stack[n].lo <= stack[n].hi

-----------------------------------------------------------------------------
(* Liveness                                                                *)

\* Every finite input array eventually leads to the terminal state.
Termination == <>(pc = "Done")

\* Once the algorithm terminates, it stays terminated with a sorted permutation.
StableResult == [](pc = "Done" => [](pc = "Done" /\ IsSorted(arr) /\ IsPerm(arr, arr0)))

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Sortedness /\ Preservation /\ PermutationInvariant
                   /\ MergePrecondition /\ MergeCorrectness /\ CopyCorrectness
                   /\ StackWellFormed)
THEOREM Spec => Termination
=============================================================================
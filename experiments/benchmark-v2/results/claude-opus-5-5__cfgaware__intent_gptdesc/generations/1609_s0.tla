------------------------------ MODULE Quicksort ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

(***************************************************************************)
(* The array is modelled abstractly as a function over Idx.  Its values    *)
(* are drawn from the finite, totally ordered domain Values.               *)
(***************************************************************************)
Idx    == 1..ArrayLen
Values == 1..(IF ArrayLen > 0 THEN ArrayLen ELSE 1)

VARIABLES
    seq,    \* the current contents of the array
    seq0,   \* the initial contents, kept for stating permutation safety
    U       \* the set of pending subranges <<lo, hi>> that still need sorting

vars == <<seq, seq0, U>>

Range(r) == r[1]..r[2]

\* All bijections of the index set onto itself
Perms == { f \in [Idx -> Idx] : \A y \in Idx : \E x \in Idx : f[x] = y }

\* Permutations that only move indices inside lo..hi
LocalPerms(lo, hi) == { f \in Perms : \A i \in Idx \ (lo..hi) : f[i] = i }

IsPermOf(t, s) == \E f \in Perms : \A i \in Idx : t[i] = s[f[i]]

Sorted(s) == \A i, j \in Idx : i < j => s[i] <= s[j]

(***************************************************************************)
(* Partitions(s, lo, hi, piv, q) is the set of arrays t such that:         *)
(*   - t rearranges only the elements of s inside lo..hi                   *)
(*     (everything outside the subarray is preserved);                     *)
(*   - the pivot element s[piv] ends up at position q;                     *)
(*   - every element left of q is <= t[q] <= every element right of q.     *)
(* So every element on the pivot's left is <= every element on its right.  *)
(***************************************************************************)
Partitions(s, lo, hi, piv, q) ==
    { t \in { [i \in Idx |-> s[f[i]]] : f \in LocalPerms(lo, hi) } :
        /\ t[q] = s[piv]
        /\ \A i \in lo..(q-1) : t[i] <= t[q]
        /\ \A j \in (q+1)..hi : t[q] <= t[j] }

\* Only subranges with at least two elements still need sorting
Sub(lo, hi) == IF lo < hi THEN {<<lo, hi>>} ELSE {}

-----------------------------------------------------------------------------

TypeOK ==
    /\ seq  \in [Idx -> Values]
    /\ seq0 \in [Idx -> Values]
    /\ U \subseteq (Idx \X Idx)
    /\ \A r \in U : r[1] < r[2]

Init ==
    /\ seq \in [Idx -> Values]
    /\ seq0 = seq
    /\ U = IF ArrayLen > 1 THEN {<<1, ArrayLen>>} ELSE {}

(***************************************************************************)
(* Atomic partition step on a pending subrange.  This step corresponds to  *)
(* one "recursive call": the range is replaced by its left and right       *)
(* subranges, which are strictly smaller.                                   *)
(***************************************************************************)
PartitionStep ==
    \E r \in U :
        LET lo == r[1]
            hi == r[2]
        IN \E piv \in lo..hi, q \in lo..hi :
             \E t \in Partitions(seq, lo, hi, piv, q) :
                /\ seq' = t
                /\ U' = (U \ {r}) \cup Sub(lo, q-1) \cup Sub(q+1, hi)
                /\ UNCHANGED seq0

\* Once nothing is left to sort, the system stutters. This avoids deadlock.
Done ==
    /\ U = {}
    /\ UNCHANGED vars

Next == PartitionStep \/ Done

\* Weak fairness on the partition step is enough for termination. The measure
\* is the sum of the sizes of the pending ranges, which strictly decreases at
\* every partition step, so it is well-founded.
Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

-----------------------------------------------------------------------------
(* Invariants and properties *)

\* Pending ranges are pairwise disjoint
DisjointRanges ==
    \A r1, r2 \in U : r1 # r2 => Range(r1) \cap Range(r2) = {}

\* Permutation preservation: no elements are lost or created
PermInv == IsPermOf(seq, seq0)

\* Partial order established by completed partitions: two indices that do
\* not lie in the same pending range are already in order.
PartialOrder ==
    \A i, j \in Idx :
        (i < j /\ ~(\E r \in U : i \in Range(r) /\ j \in Range(r)))
            => seq[i] <= seq[j]

\* Safety: at completion, the array is a sorted permutation of the input
SortedWhenDone == (U = {}) => (Sorted(seq) /\ IsPermOf(seq, seq0))

Safety == TypeOK /\ DisjointRanges /\ PermInv /\ PartialOrder /\ SortedWhenDone

\* Well-founded termination measure
Measure == LET RECURSIVE SumSz(_)
               SumSz(S) == IF S = {} THEN 0
                           ELSE LET r == CHOOSE x \in S : TRUE
                                IN (r[2] - r[1] + 1) + SumSz(S \ {r})
           IN SumSz(U)

\* No interference: elements outside every pending subrange never change
NoInterference ==
    [][\A i \in Idx : (\A r \in U : i \notin Range(r)) => seq'[i] = seq[i]]_vars

\* Liveness: quicksort terminates
Termination == <>(U = {})

\* Liveness: the final array is sorted and is a permutation of the input
EventuallySorted == <>[](Sorted(seq) /\ IsPermOf(seq, seq0))

=============================================================================
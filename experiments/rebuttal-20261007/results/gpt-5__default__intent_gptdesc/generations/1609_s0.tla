----------------------------- MODULE Quicksort -----------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
  N,        \* Fixed array length
  Val       \* Finite set of comparable integer values (domain of elements)

ASSUME /\ N \in Nat
       /\ IsFinite(Val)
       /\ Val \subseteq Int

(*
  Indices and intervals
*)
Indices == 1..N

Interval == [lo : Indices, hi : Indices]

IsInterval(seg) == seg \in Interval /\ seg.lo <= seg.hi

NeedSort(seg) == seg.hi - seg.lo >= 1

AllIntervals == { s \in Interval : s.lo <= s.hi }

(*
  Multi-set (permutation) equality for sequences over Val
*)
CountVal(s, v) ==
  Cardinality({ i \in 1..Len(s) : s[i] = v })

Perm(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Val : CountVal(s, v) = CountVal(t, v)

(*
  Sortedness
*)
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

(*
  Utility: measure of outstanding work (sum of interval lengths)
*)
LenSeg(seg) == seg.hi - seg.lo + 1

RECURSIVE SumLen(_)
SumLen(S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE IN
      LenSeg(x) + SumLen(S \ {x})

(*
  Variables:
    A  - current array (sequence over Val of fixed length N)
    A0 - initial array, remembered to state permutation preservation
    Work - finite set of intervals [lo..hi] still to be processed (length >= 2)
*)
VARIABLES A, A0, Work

vars == << A, Work, A0 >>

(*
  Initialization
*)
Init ==
  /\ A \in Seq(Val)
  /\ Len(A) = N
  /\ A0 = A
  /\ Work =
       IF N >= 2
       THEN { [lo |-> 1, hi |-> N] }
       ELSE {}

(*
  Partition step:
    - Choose an interval [l..r] from Work with r-l+1 >= 2
    - Choose a pivot index p in [l..r] and a target position q in [l..r]
    - Choose a rearrangement A2 that:
        * keeps elements outside [l..r] unchanged
        * is a permutation of A over [l..r]
        * places the pivot value A[p] at position q
        * ensures every element on [l..q] is <= every element on [q+1..r]
    - Replace [l..r] in Work with its left/right subintervals that still need sorting
*)
PartitionStep ==
  \E seg \in Work :
    LET l == seg.lo IN
    LET r == seg.hi IN
    \E p \in l..r :
    \E q \in l..r :
    \E A2 \in Seq(Val) :
      /\ Len(A2) = N
      /\ \A i \in Indices \ (l..r) : A2[i] = A[i]
      /\ Perm(SubSeq(A2, l, r), SubSeq(A, l, r))
      /\ A2[q] = A[p]
      /\ \A i \in l..q : \A j \in (q+1)..r : A2[i] <= A2[j]
      /\ A' = A2
      /\ Work' =
           (Work \ {seg})
           \cup (IF q - l >= 1 THEN { [lo |-> l,     hi |-> q - 1] } ELSE {})
           \cup (IF r - q >= 1 THEN { [lo |-> q + 1, hi |-> r     ] } ELSE {})
      /\ A0' = A0

(*
  Next-state relation allows either a partition step or stuttering.
*)
Next ==
  PartitionStep \/ UNCHANGED vars

(*
  Invariants:
    - Typing/structure of variables
    - Work contains only intervals of length >= 2 and is pairwise disjoint
    - Global permutation preservation: A is always a permutation of A0
    - Partial ordering established by completed partitions:
        For any i < j not both contained in a single outstanding interval,
        A[i] <= A[j].
*)
PairwiseDisjoint(WS) ==
  \A s, t \in WS :
    s = t \/ (s.hi < t.lo) \/ (t.hi < s.lo)

WorkWellFormed ==
  /\ Work \subseteq { s \in AllIntervals : NeedSort(s) }
  /\ PairwiseDisjoint(Work)

TypeInv ==
  /\ A \in Seq(Val)
  /\ Len(A) = N
  /\ WorkWellFormed

PermInv ==
  Perm(A, A0)

SpannedByWork(i, j) ==
  \E seg \in Work : seg.lo <= i /\ j <= seg.hi

POInv ==
  \A i, j \in Indices :
    (i < j /\ ~SpannedByWork(i, j)) => A[i] <= A[j]

Inv == TypeInv /\ PermInv /\ POInv

(*
  Completion and liveness
*)
Done == Work = {}

Termination == <> Done

(*
  Safety bundle for convenience
*)
Safety ==
  /\ []PermInv
  /\ [](Done => Sorted(A))

(*
  Decrease of the well-founded measure on partition steps
*)
Decreases ==
  PartitionStep => SumLen(Work') < SumLen(Work)

(*
  Full system specification with weak fairness ensuring progress
*)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

=============================================================================
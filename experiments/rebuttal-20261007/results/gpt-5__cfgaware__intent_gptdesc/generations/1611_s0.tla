---------------------------- MODULE MERGESORT ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

(*
  Abstract, nondeterministic mergesort over a fixed-length sequence of integers.
  The array A is updated in-place only by replacing contiguous ranges via Write/WriteRange.
  The control is represented by a partition of the index space into contiguous segments
  (each marked sorted or unsorted). Actions:
    - Split: split an unsorted segment into two (nearly) halves, both unsorted.
    - BaseMark: mark a length-1 unsorted segment as sorted.
    - Merge: merge two adjacent sorted segments by replacing their combined range
             with any sorted sequence that is a permutation of that range.
*)

CONSTANTS
  ArrayLen,          \* Nonnegative length of the array to sort
  defaultInitValue   \* Unused here; provided to satisfy tooling that binds this name

VARIABLES
  A,     \* Current array (sequence) of integers of length ArrayLen
  A0,    \* Snapshot of the initial array (constant across behaviors)
  Segs   \* Sequence of records [l, r, sorted] forming a contiguous partition of 1..ArrayLen

vars == << A, Segs, A0 >>

(***************************************************************************)
(* Basic sequence and array helpers                                        *)
(***************************************************************************)

IsSeqInt(s) == /\ s \in Seq(Int)

IsSorted(s) ==
  LET n == Len(s) IN
    \A i, j \in 1..n : (i < j) => s[i] <= s[j]

SubArr(a, l, r) == SubSeq(a, l, r)

Count(s, x) ==
  Cardinality({ i \in 1..Len(s) : s[i] = x })

Bag(s) ==
  [ x \in Int |-> Count(s, x) ]

Read(a, i) == a[i]

Write(a, i, v) ==
  [ j \in 1..Len(a) |-> IF j = i THEN v ELSE a[j] ]

WriteRange(a, l, r, s) ==
  [ i \in 1..Len(a) |-> IF l <= i /\ i <= r THEN s[i - l + 1] ELSE a[i] ]

MakeSeg(l, r, sorted) == [l |-> l, r |-> r, sorted |-> sorted]

RangeLen(seg) == seg.r - seg.l + 1

ReplaceAt(seq, i, repl) ==
  SubSeq(seq, 1, i-1) \o repl \o SubSeq(seq, i+1, Len(seq))

PartitionOK(segs) ==
  IF ArrayLen = 0 THEN Len(segs) = 0
  ELSE
    /\ Len(segs) >= 1
    /\ segs[1].l = 1
    /\ segs[Len(segs)].r = ArrayLen
    /\ \A k \in 1..Len(segs) : segs[k].l <= segs[k].r
    /\ \A k \in 1..(Len(segs)-1) : segs[k].r + 1 = segs[k+1].l

Done ==
  IF ArrayLen = 0 THEN TRUE
  ELSE /\ Len(Segs) = 1
       /\ Segs[1].sorted
       /\ Segs[1].l = 1
       /\ Segs[1].r = ArrayLen

(***************************************************************************)
(* Merge-correctness operator                                               *)
(***************************************************************************)

MergeOK(l, m, r, a, b) ==
  /\ 1 <= l /\ l <= m /\ m < r /\ r <= Len(a)
  /\ IsSorted(SubArr(a, l, m))
  /\ IsSorted(SubArr(a, m+1, r))
  /\ \E s \in Seq(Int) :
        /\ Len(s) = r - l + 1
        /\ IsSorted(s)
        /\ Bag(s) = Bag(SubArr(a, l, r))
        /\ b = WriteRange(a, l, r, s)

(***************************************************************************)
(* Initialization                                                           *)
(***************************************************************************)

Init ==
  /\ ArrayLen \in Nat
  /\ A \in [1..ArrayLen -> Int]
  /\ A0 = A
  /\ IF ArrayLen = 0
        THEN Segs = << >>
        ELSE Segs = << MakeSeg(1, ArrayLen, FALSE) >>

(***************************************************************************)
(* Transitions                                                              *)
(***************************************************************************)

Split ==
  \E i \in 1..Len(Segs) :
    LET s == Segs[i] IN
    /\ ~s.sorted
    /\ RangeLen(s) >= 2
    /\ LET l == s.l IN
       LET r == s.r IN
       LET m == l + (r - l) \div 2 IN
         /\ A' = A
         /\ Segs' =
              ReplaceAt(Segs, i,
                        << MakeSeg(l, m, FALSE),
                           MakeSeg(m+1, r, FALSE) >>)
         /\ A0' = A0

BaseMark ==
  \E i \in 1..Len(Segs) :
    LET s == Segs[i] IN
      /\ ~s.sorted
      /\ RangeLen(s) = 1
      /\ A' = A
      /\ Segs' = ReplaceAt(Segs, i, << MakeSeg(s.l, s.r, TRUE) >>)
      /\ A0' = A0

Merge ==
  \E i \in 1..(Len(Segs) - 1) :
    LET s1 == Segs[i] IN
    LET s2 == Segs[i+1] IN
      /\ s1.sorted /\ s2.sorted
      /\ s1.r + 1 = s2.l
      /\ LET l == s1.l IN
         LET m == s1.r IN
         LET r == s2.r IN
           /\ \E s \in Seq(Int) :
                /\ Len(s) = r - l + 1
                /\ IsSorted(SubArr(A, l, m))
                /\ IsSorted(SubArr(A, m+1, r))
                /\ IsSorted(s)
                /\ Bag(s) = Bag(SubArr(A, l, r))
                /\ A' = WriteRange(A, l, r, s)
           /\ Segs' = ReplaceAt(Segs, i, << MakeSeg(l, r, TRUE) >>)
           /\ A0' = A0

Next == Split \/ BaseMark \/ Merge

(***************************************************************************)
(* Variant (for reasoning about termination; not used by TLC)               *)
(***************************************************************************)

UMeasure ==
  \E segs \in {Segs} :
    \* Sum over unsorted segments of (len - 1)
    LET idxs == 1..Len(Segs) IN
      SumSet({ RangeLen(Segs[k]) - 1 : k \in idxs, ~Segs[k].sorted })
\* Helper: Sum of a finite set of natural numbers (defined via recursion over a set)
SumSet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumSet(S \ {x})

UCount == Cardinality({ k \in 1..Len(Segs) : ~Segs[k].sorted })
SCount == Cardinality({ k \in 1..Len(Segs) :  Segs[k].sorted })
Variant == << UMeasure, UCount, SCount >>

(***************************************************************************)
(* Specification, Invariant, and Liveness                                   *)
(***************************************************************************)

TypeOK ==
  /\ A \in [1..ArrayLen -> Int]
  /\ A0 \in [1..ArrayLen -> Int]
  /\ PartitionOK(Segs)

PermutationPreserved == Bag(A) = Bag(A0)

SegmentSortedness ==
  \A i \in 1..Len(Segs) :
    Segs[i].sorted => IsSorted(SubArr(A, Segs[i].l, Segs[i].r))

Invariant ==
  /\ TypeOK
  /\ SegmentSortedness
  /\ PermutationPreserved
  /\ (Done => IsSorted(A))

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(Split) /\ WF_vars(BaseMark) /\ WF_vars(Merge)

Termination == []<>(Done)

=============================================================================
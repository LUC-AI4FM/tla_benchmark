------------------------------- MODULE NDQuicksort -------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  N,            \* array length
  Val,          \* totally ordered value domain
  LE,           \* total order relation on Val
  A0            \* initial array

(*
  Basic order axioms for LE over Val.
*)
IsTotalOrder(R, S) ==
  /\ R \subseteq S \X S
  /\ \A x \in S : <<x, x>> \in R
  /\ \A x, y \in S : (<<x, y>> \in R /\ <<y, x>> \in R) => x = y
  /\ \A x, y, z \in S : (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R
  /\ \A x, y \in S : (<<x, y>> \in R) \/ (<<y, x>> \in R)

ASSUME
  /\ N \in Nat
  /\ A0 \in [ (IF N = 0 THEN {} ELSE 1..N) -> Val ]
  /\ IsTotalOrder(LE, Val)

Idx == IF N = 0 THEN {} ELSE 1..N

LEQ(x, y) == <<x, y>> \in LE

Range(lo, hi) == IF lo <= hi THEN lo..hi ELSE {}

CountInSet(A, S, v) == Cardinality({ i \in S : A[i] = v })

PermInSet(A, B, S) ==
  \A v \in Val : CountInSet(A, S, v) = CountInSet(B, S, v)

Perm(A, B) == PermInSet(A, B, Idx)

Sorted(A) ==
  \A i \in (IF N <= 1 THEN {} ELSE 1..(N-1)) : LEQ(A[i], A[i+1])

VARIABLES
  A,           \* current array (sequence over Val)
  Pending      \* set of pending intervals as pairs <<lo, hi>>

TypeOK ==
  /\ A \in [Idx -> Val]
  /\ Pending \subseteq (Idx \X Idx)

(*
  A partition step is any in-place rearrangement inside [lo,hi] for a chosen
  pivot p with lo <= p < hi that:
  - leaves A unchanged outside [lo,hi],
  - is a permutation of the subarray A[lo..hi],
  - ensures all elements in [lo..p] are <= all elements in [p+1..hi].
*)
PartitionOK(A, B, lo, hi, p) ==
  /\ lo \in Idx /\ hi \in Idx /\ p \in Idx
  /\ lo <= p /\ p < hi
  /\ B \in [Idx -> Val]
  /\ \A i \in (Idx \ Range(lo, hi)) : B[i] = A[i]
  /\ PermInSet(A, B, Range(lo, hi))
  /\ \A i \in Range(lo, p) : \A j \in Range(p+1, hi) : LEQ(B[i], B[j])

Remove(lo, hi) ==
  /\ <<lo, hi>> \in Pending
  /\ lo \in Idx /\ hi \in Idx
  /\ lo >= hi
  /\ A' = A
  /\ Pending' = Pending \ {<<lo, hi>>}

DoPartition(lo, hi) ==
  /\ <<lo, hi>> \in Pending
  /\ lo \in Idx /\ hi \in Idx
  /\ lo < hi
  /\ \E p \in lo..(hi-1), B \in [Idx -> Val] :
       /\ PartitionOK(A, B, lo, hi, p)
       /\ A' = B
       /\ Pending' = (Pending \ {<<lo, hi>>})
                      \cup {<<lo, p>>, <<p+1, hi>>}

Init ==
  /\ A = A0
  /\ Pending = (IF N = 0 THEN {} ELSE {<<1, N>>})
  /\ TypeOK

Next ==
  \E lo \in Idx, hi \in Idx :
    Remove(lo, hi) \/ DoPartition(lo, hi)

Touched == { i \in Idx : A'[i] # A[i] }

(*
  Fairness to prevent starvation of any enabled interval handling
  (either removing a base case interval or partitioning a nontrivial one).
*)
Fairs ==
  /\ \A lo \in Idx, hi \in Idx : WF_<<A, Pending>>(Remove(lo, hi))
  /\ \A lo \in Idx, hi \in Idx : WF_<<A, Pending>>(DoPartition(lo, hi))

Spec == Init /\ [][Next]_<<A, Pending>> /\ Fairs

(*
  Safety properties (as invariants):
  - Type correctness.
  - Global multiset (bag) of array elements equals that of the original array.
  - Each step only modifies positions within the currently handled interval.
*)
Inv_TypeOK == []TypeOK

Inv_MultisetPreserved == [](Perm(A, A0))

Inv_PreserveOutside ==
  []( \E lo \in Idx, hi \in Idx :
        (Remove(lo, hi) \/ DoPartition(lo, hi))
        /\ Touched \subseteq Range(lo, hi) )

Safety == Inv_TypeOK /\ Inv_MultisetPreserved /\ Inv_PreserveOutside

(*
  Ordering progress: when no work remains, the array is sorted.
*)
OrderingProgress == [](Pending = {} => Sorted(A))

(*
  Liveness/termination: under the fairness assumptions, the algorithm
  eventually reaches a state with no pending intervals.
*)
Termination == <>(Pending = {})

=============================================================================
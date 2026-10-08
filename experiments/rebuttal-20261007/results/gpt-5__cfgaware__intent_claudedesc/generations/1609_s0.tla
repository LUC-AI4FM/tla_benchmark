--------------------------- MODULE Quicksort ---------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANT ArrayLen

(*
  Assumption on the configurable array length.
  Model checking can instantiate ArrayLen with small naturals such as 4 or 5.
*)
ASSUME ArrayLen \in Nat /\ ArrayLen >= 1

(*
  Index and value ranges. Values are taken from the same range as indices.
*)
Indices == 1..ArrayLen
Values  == 1..ArrayLen

(*
  Helper: inclusive index range as a set (empty if i > j).
*)
Range(i, j) == { k \in Indices : i <= k /\ k <= j }

(*
  Counting occurrences of a value v in array A over a set of indices S.
*)
Count(A, S, v) == Cardinality({ i \in S : A[i] = v })

(*
  Permutation on a subrange S: equal multiplicities within S and equality outside S.
*)
PermutesOn(A, B, S) ==
  /\ \A v \in Values : Count(A, S, v) = Count(B, S, v)
  /\ \A i \in (Indices \ S) : B[i] = A[i]

(*
  Global sortedness: non-decreasing with respect to index order.
*)
Sorted(A) == \A i, j \in Indices : i <= j => A[i] <= A[j]

(*
  Abstract partitioning w.r.t. a chosen pivot position k in [i..j]:
  - B is a permutation of A on [i..j], unchanged outside;
  - all elements at positions <= k are <= all elements at positions > k within [i..j].
*)
Partition(A, i, j, k, B) ==
  /\ i \in Indices /\ j \in Indices /\ k \in Indices
  /\ i <= k /\ k <= j
  /\ PermutesOn(A, B, Range(i, j))
  /\ \A p \in Range(i, k) : \A q \in Range(k+1, j) : B[p] <= B[q]

(*
  State variables:
    - A  : current in-place array
    - A0 : original array (constant across steps)
    - Pending : set of subarray intervals <<i, j>> (with i < j) still to process
*)
VARIABLES A, A0, Pending

(*
  Initialisation:
    - A is any mapping Indices -> Values (nondeterministic initialization)
    - Pending contains the full interval if its length is at least 2, else empty
    - A0 captures the original array
*)
Init ==
  /\ A \in [Indices -> Values]
  /\ Pending =
       IF ArrayLen >= 2 THEN { <<1, ArrayLen>> }
       ELSE {}
  /\ A0 = A

(*
  One quicksort step:
    - pick an interval <<i, j>> with i < j from Pending
    - pick a pivot index k with i <= k <= j
    - pick any B that is a valid partitioned permutation on [i..j]
    - update A to B
    - replace <<i, j>> in Pending by subintervals excluding the pivot position k
      and include only those subintervals whose length is at least 2
*)
QuicksortStep ==
  \E i, j \in Indices :
    /\ <<i, j>> \in Pending
    /\ i < j
    /\ \E k \in Indices :
         /\ i <= k /\ k <= j
         /\ \E B \in [Indices -> Values] :
              /\ Partition(A, i, j, k, B)
              /\ A' = B
              /\ Pending' =
                   (Pending \ { <<i, j>> }) \/
                   (IF i + 1 < k THEN { <<i, k-1>> } ELSE {}) \/
                   (IF k + 1 < j THEN { <<k+1, j>> } ELSE {})
              /\ A0' = A0

Next == QuicksortStep

(*
  Completion predicate and temporal specification with weak fairness to rule out
  infinite stuttering while work remains.
*)
Done == Pending = {}

Spec ==
  Init /\ [][Next]_<A, Pending, A0> /\ WF_<A, Pending, A0>(Next)

(*
  Liveness property: the algorithm eventually terminates (no pending subarrays).
*)
Termination == <>Done

(*
  Optional safety property (not required by configuration):
  Upon termination, the final array is a permutation of the original and sorted.
*)
Safety == [](Done => (PermutesOn(A0, A, Indices) /\ Sorted(A)))

=======================================================================
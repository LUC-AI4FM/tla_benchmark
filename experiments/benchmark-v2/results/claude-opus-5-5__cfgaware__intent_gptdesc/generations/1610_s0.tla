---------------------------- MODULE NondetQuicksort ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat

(***************************************************************************)
(* Domain: array positions 1..N, values drawn from the totally ordered     *)
(* finite domain Values (natural numbers ordered by <=).                   *)
(***************************************************************************)
Indices == 1..N
Values  == 1..(IF N = 0 THEN 1 ELSE N)

VARIABLES arr, arr0, pending

vars == <<arr, arr0, pending>>

Interval(lo, hi) == {i \in Indices : lo <= i /\ i <= hi}

Count(a, v) == Cardinality({i \in Indices : a[i] = v})

IsPermutationOf(a, b) == \A v \in Values : Count(a, v) = Count(b, v)

Sorted(a) == \A i, j \in Indices : i <= j => a[i] <= a[j]

(* Bijections of Indices that move only positions inside [lo, hi]. *)
LocalPerms(lo, hi) ==
  { f \in [Indices -> Indices] :
      /\ \A v \in Indices : \E i \in Indices : f[i] = v
      /\ \A i \in Indices : i \notin Interval(lo, hi) => f[i] = i }

(* Every result of a legal partition step on [lo,hi] with pivot p. *)
Partitions(a, lo, hi, p) ==
  { b \in { [i \in Indices |-> a[f[i]]] : f \in LocalPerms(lo, hi) } :
      \A i \in Interval(lo, p) : \A j \in Interval(p + 1, hi) : b[i] <= b[j] }

TypeOK ==
  /\ arr \in [Indices -> Values]
  /\ arr0 \in [Indices -> Values]
  /\ pending \subseteq (Nat \X Nat)

Init ==
  /\ arr0 \in [Indices -> Values]
  /\ arr = arr0
  /\ pending = {<<1, N>>}

PartitionStep(lo, hi) ==
  /\ <<lo, hi>> \in pending
  /\ lo < hi
  /\ \E p \in lo..(hi - 1) :
       /\ arr' \in Partitions(arr, lo, hi, p)
       /\ pending' = (pending \ {<<lo, hi>>}) \cup {<<lo, p>>, <<p + 1, hi>>}
  /\ UNCHANGED arr0

DropTrivial(lo, hi) ==
  /\ <<lo, hi>> \in pending
  /\ lo >= hi
  /\ pending' = pending \ {<<lo, hi>>}
  /\ UNCHANGED <<arr, arr0>>

Step == \E iv \in pending : PartitionStep(iv[1], iv[2]) \/ DropTrivial(iv[1], iv[2])

Done == pending = {} /\ UNCHANGED vars

Next == Step \/ Done

(* Weak fairness: an enabled step cannot be starved forever. *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety *)
PermutationInv == IsPermutationOf(arr, arr0)

(* Pending intervals are pairwise disjoint and every pair of positions not *)
(* inside a common pending interval is already correctly ordered.          *)
Covered(i) == \E iv \in pending : i \in Interval(iv[1], iv[2])
SameInterval(i, j) ==
  \E iv \in pending : i \in Interval(iv[1], iv[2]) /\ j \in Interval(iv[1], iv[2])
OrderInv ==
  \A i, j \in Indices : (i < j /\ ~SameInterval(i, j)) => arr[i] <= arr[j]

(* Steps preserve the multiset and leave values outside [lo,hi] intact. *)
StepSafety ==
  [][ \A iv \in pending :
        PartitionStep(iv[1], iv[2]) =>
          /\ IsPermutationOf(arr', arr)
          /\ \A i \in Indices : i \notin Interval(iv[1], iv[2]) => arr'[i] = arr[i]
    ]_vars

(* Ordering: no pending intervals implies sorted. *)
SortedWhenDone == pending = {} => Sorted(arr)

(* Liveness *)
Termination == <>(pending = {})

THEOREM Spec => [](TypeOK /\ PermutationInv /\ OrderInv /\ SortedWhenDone)
THEOREM Spec => Termination
=============================================================================
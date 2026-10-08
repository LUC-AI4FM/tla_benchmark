----------------------------- MODULE Quicksort -----------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

(*
  Index set for the array.
*)
Idx == 1..N

(*
  Variables:
    A  - current array (function from indices to values)
    A0 - initial array snapshot (constant across behavior)
    S  - set of intervals still to process; intervals are records [l |-> ..., r |-> ...]
*)
VARIABLES A, A0, S

vars == << A, S, A0 >>

(*
  Interval utilities.
*)
IsInterval(iv) ==
  iv \in [l : Idx, r : Idx] /\ iv.l <= iv.r

IvLen(iv) == iv.r - iv.l + 1

AllIntervals == { iv \in [l : Idx, r : Idx] : iv.l <= iv.r }

(*
  Permutation helper on a set I of indices.
  p is a permutation of I iff it is a bijection I -> I.
*)
OneToOne(p, I) == \A i, j \in I : (i # j) => p[i] # p[j]
RangeOf(p, I) == { p[i] : i \in I }
IsPermMap(p, I) == p \in [I -> I] /\ OneToOne(p, I) /\ RangeOf(p, I) = I

(*
  g is obtained from f by permuting the entries on I according to some bijection,
  with all entries outside I unchanged (the "outside unchanged" part is used
  separately where needed).
*)
PermutesOnRange(f, g, I) ==
  \E p \in [I -> I] :
    IsPermMap(p, I) /\ \A i \in I : g[i] = f[p[i]]

(*
  New intervals produced by choosing pivot p in interval iv:
    - left:  [iv.l .. p-1] if iv.l <= p-1
    - right: [p    .. iv.r]  (always non-empty because p \in iv.l..iv.r)
*)
NewIntervals(iv, p) ==
  LET leftSet ==
        IF iv.l <= p - 1
          THEN { [l |-> iv.l, r |-> p - 1] }
          ELSE {}
      rightSet ==
        { [l |-> p, r |-> iv.r] }
  IN leftSet \cup rightSet

(*
  Partition correctness for rearranging subarray iv.l..iv.r around pivot index p:
    - the subarray is a permutation of the old subarray;
    - every element left of p is <= every element at/after p;
    - elements outside iv.l..iv.r are unchanged.
*)
PartitionOk(f, g, iv, p) ==
  LET J == iv.l..iv.r
  IN /\ PermutesOnRange(f, g, J)
     /\ \A k \in Idx \ J : g[k] = f[k]
     /\ \A i \in iv.l..(p - 1) : \A j \in p..iv.r : g[i] <= g[j]

(*
  Initialization:
    - array arbitrary in [1..N -> 1..N]
    - initial interval is the whole array
    - A0 stores the initial array
*)
Init ==
  /\ A \in [Idx -> Idx]
  /\ S = { [l |-> 1, r |-> N] }
  /\ A0 = A

(*
  Actions:
    - RemoveTrivial: pick an interval of length 1 and remove it.
    - PartitionAny:  pick a non-trivial interval and any pivot in it; rearrange accordingly.
    - PartitionNonExtreme: like PartitionAny but pivot strictly greater than left bound (p \in iv.l+1..iv.r),
                           guaranteeing that the right interval has length 1 (progress-producing).
*)
RemoveTrivial ==
  \E iv \in S :
    /\ IvLen(iv) <= 1
    /\ A' = A
    /\ S' = S \ { iv }
    /\ A0' = A0

PartitionAny ==
  \E iv \in S :
    /\ IvLen(iv) >= 2
    /\ \E p \in iv.l..iv.r :
      \E Aprime \in [Idx -> Idx] :
        /\ PartitionOk(A, Aprime, iv, p)
        /\ A' = Aprime
        /\ S' = (S \ { iv }) \cup NewIntervals(iv, p)
        /\ A0' = A0

PartitionNonExtreme ==
  \E iv \in S :
    /\ IvLen(iv) >= 2
    /\ \E p \in (iv.l + 1)..iv.r :
      \E Aprime \in [Idx -> Idx] :
        /\ PartitionOk(A, Aprime, iv, p)
        /\ A' = Aprime
        /\ S' = (S \ { iv }) \cup NewIntervals(iv, p)
        /\ A0' = A0

Next ==
  RemoveTrivial \/ PartitionAny

(*
  Termination predicate.
*)
Terminated == S = {}

(*
  Typing and basic safety invariants.
*)
TypeInv ==
  /\ A \in [Idx -> Idx]
  /\ A0 \in [Idx -> Idx]
  /\ S \subseteq AllIntervals

PermInv == PermutesOnRange(A0, A, Idx)

Safety == TypeInv /\ PermInv

(*
  Full specification with fairness:
    - Always allow stuttering when no intervals remain.
    - Weak fairness on RemoveTrivial ensures singleton intervals are eventually removed.
    - Strong fairness on PartitionNonExtreme ensures that when non-trivial intervals exist,
      we eventually perform a progress-producing partition (pivot strictly > left bound),
      preventing infinite non-progress partitions.
*)
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RemoveTrivial)
  /\ SF_vars(PartitionNonExtreme)

(*
  Liveness property: algorithm always eventually terminates.
*)
Termination == <> Terminated

=============================================================================
--------------------------- MODULE QuicksortPlusCal ---------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat

(*
  Basic sets and helper definitions
*)
Indices == 1..N

Intervals == { <<l, r>> \in (Indices \X Indices) : l < r }

Count(arr, v) == Cardinality({ i \in Indices : arr[i] = v })

Permutation(arr1, arr2) == \A v \in Indices : Count(arr1, v) = Count(arr2, v)

Partition(i, j, k, arr) ==
  /\ i \in Indices
  /\ j \in Indices
  /\ i <= j
  /\ k \in i..j
  /\ \A m \in i..(k-1) : arr[m] <= arr[k]
  /\ \A m \in (k+1)..j : arr[m] >= arr[k]

(*
  Variables
*)
VARIABLES A, S, pc

vars == << A, S, pc >>

(*
  State predicates
*)
TypeOK ==
  /\ A \in [Indices -> Indices]
  /\ S \subseteq Intervals
  /\ pc \in {"qs1", "Done"}

Init ==
  /\ A \in [Indices -> Indices]
  /\ S = IF N >= 2 THEN { <<1, N>> } ELSE {}
  /\ pc = IF N >= 2 THEN "qs1" ELSE "Done"

(*
  Single control-location action qs1:
    - If S is nonempty: choose an interval <<i,j>> in S, choose a pivot k in i..j,
      and replace A by any permutation aNew of A that satisfies the partition
      ordering around k within i..j. Update S by removing <<i,j>> and adding any
      proper subintervals (length >= 2) on the left/right of k.
    - If S is empty: move to Done.
*)
qs1 ==
  /\ pc = "qs1"
  /\ ( /\ S # {}
       /\ \E i, j \in Indices :
            /\ <<i, j>> \in S
            /\ \E k \in i..j :
                \E aNew \in [Indices -> Indices] :
                  /\ Permutation(aNew, A)
                  /\ Partition(i, j, k, aNew)
                  /\ A' = aNew
                  /\ S' =
                       (S \ { <<i, j>> })
                       \cup (IF i < k-1 THEN { <<i, k-1>> } ELSE {})
                       \cup (IF k+1 < j THEN { <<k+1, j>> } ELSE {})
                  /\ pc' = "qs1"
     )
     \/ ( /\ S = {}
          /\ pc' = "Done"
          /\ UNCHANGED << A, S >>
        )

Next == qs1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
  Safety invariant: well-typed states
*)
Inv == TypeOK

(*
  Liveness: eventual termination (eventually reach Done)
*)
Termination == <> (pc = "Done")

=============================================================================
---- MODULE QuickSort ----
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Idx == 1..N

VARIABLES A, A0, U, pc

vars == <<A, A0, U, pc>>

Perms == { f \in [Idx -> Idx] : \A y \in Idx : \E x \in Idx : f[x] = y }

PermsOf(Arr) == { [i \in Idx |-> Arr[f[i]]] : f \in Perms }

IsPermOf(B, C) == \E f \in Perms : \A i \in Idx : B[i] = C[f[i]]

IsSorted(B) == \A i, j \in Idx : (i < j) => (B[i] <= B[j])

Partitions(B, p, lo, hi) ==
  { C \in PermsOf(B) :
      /\ \A i \in Idx : (i < lo \/ i > hi) => C[i] = B[i]
      /\ \A i \in lo..p, j \in (p+1)..hi : C[i] <= C[j] }

SubRanges(lo, p, hi) ==
  (IF lo < p THEN {<<lo, p>>} ELSE {})
  \cup (IF p + 1 < hi THEN {<<p + 1, hi>>} ELSE {})

TypeOK ==
  /\ A \in [Idx -> Idx]
  /\ A0 \in [Idx -> Idx]
  /\ U \subseteq (Idx \X Idx)
  /\ pc \in {"a", "Done"}

Init ==
  /\ A \in [Idx -> Idx]
  /\ A0 = A
  /\ U = IF N > 1 THEN {<<1, N>>} ELSE {}
  /\ pc = "a"

PartitionStep ==
  /\ pc = "a"
  /\ U # {}
  /\ \E r \in U :
       LET lo == r[1]
           hi == r[2]
       IN \E p \in lo..(hi - 1) :
            \E C \in Partitions(A, p, lo, hi) :
               /\ A' = C
               /\ U' = (U \ {r}) \cup SubRanges(lo, p, hi)
  /\ UNCHANGED <<A0, pc>>

Finish ==
  /\ pc = "a"
  /\ U = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<A, A0, U>>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == PartitionStep \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep \/ Finish)

PermutationInv == IsPermOf(A, A0)

UnsortedRangesValid ==
  \A r \in U : r[1] < r[2] /\ r[1] \in Idx /\ r[2] \in Idx

PartialCorrectness ==
  (pc = "Done") => (IsPermOf(A, A0) /\ IsSorted(A))

Termination == <>(pc = "Done")

THEOREM Spec => []TypeOK
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination
====
------------------------------ MODULE QuickSort ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

VARIABLES A,   \* the array being sorted
          A0,  \* the original array, kept so permutation can be checked
          U    \* the set of subarray ranges <<lo, hi>> still to be sorted

vars == <<A, A0, U>>

Indices == 1..ArrayLen
Values  == 1..ArrayLen

\* All bijections of a finite set S onto itself
Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }

\* All permutations of an array
PermsOf(Arr) ==
    { [i \in DOMAIN Arr |-> Arr[f[i]]] : f \in Automorphisms(DOMAIN Arr) }

\* All valid partitions of B on range lo..hi around pivot index p.
\* Elements outside lo..hi are not changed. Every element in lo..p is
\* no greater than every element in p+1..hi.
Partitions(B, p, lo, hi) ==
    { C \in PermsOf(B) :
        /\ \A i \in Indices \ (lo..hi) : C[i] = B[i]
        /\ \A i \in lo..p : \A j \in (p+1)..hi : C[i] <= C[j] }

IsSorted(Arr) == \A i, j \in Indices : i < j => Arr[i] <= Arr[j]

TypeOK ==
    /\ A  \in [Indices -> Values]
    /\ A0 \in [Indices -> Values]
    /\ U  \subseteq (Indices \X Indices)

Init ==
    /\ A \in [Indices -> Values]
    /\ A0 = A
    /\ U = IF ArrayLen > 0 THEN { <<1, ArrayLen>> } ELSE {}

\* Partition a range of length >= 2, then add both halves as pending work
PartitionStep(r) ==
    LET lo == r[1]
        hi == r[2]
    IN  /\ lo < hi
        /\ \E p \in lo..(hi - 1) :
             /\ A' \in Partitions(A, p, lo, hi)
             /\ U' = (U \ {r}) \cup { <<lo, p>>, <<p + 1, hi>> }
        /\ UNCHANGED A0

\* A range of length <= 1 is already sorted
TrivialStep(r) ==
    /\ r[1] >= r[2]
    /\ U' = U \ {r}
    /\ UNCHANGED <<A, A0>>

\* Stutter after termination, so the finished state is not a deadlock
Done ==
    /\ U = {}
    /\ UNCHANGED vars

Next ==
    \/ \E r \in U : PartitionStep(r) \/ TrivialStep(r)
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness: the algorithm always terminates
Termination == <>(U = {})

\* Safety: on termination the array is a sorted permutation of the original
PartialCorrectness ==
    (U = {}) => (A \in PermsOf(A0) /\ IsSorted(A))

Correctness == []PartialCorrectness

=============================================================================
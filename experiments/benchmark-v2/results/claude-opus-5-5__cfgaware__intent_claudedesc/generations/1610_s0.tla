---------------------------- MODULE QuickSort ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

VARIABLES seq, seq0, U

vars == <<seq, seq0, U>>

Indices == 1..N

(* Permutation helper: all bijections of a finite set S onto itself *)
Perms(S) == {f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y}

(* All rearrangements of s within interval I = <<lo, hi>> such that every
   element at positions lo..p is <= every element at positions p+1..hi,
   with elements outside the interval unchanged. *)
Partitions(I, p, s) ==
  LET lo == I[1]
      hi == I[2]
      R  == lo..hi
      Rearranged == { [i \in Indices |-> IF i \in R THEN s[f[i]] ELSE s[i]] :
                        f \in Perms(R) }
  IN  { t \in Rearranged :
          \A i \in lo..p : \A j \in (p+1)..hi : t[i] <= t[j] }

TypeOK ==
  /\ seq \in [Indices -> 1..N]
  /\ seq0 \in [Indices -> 1..N]
  /\ U \subseteq (Indices \X Indices) \cup {<<i, j>> : i \in 1..(N+1), j \in 0..N}

Init ==
  /\ seq \in [Indices -> 1..N]
  /\ seq0 = seq
  /\ U = {<<1, N>>}

Step ==
  \E I \in U :
    IF I[1] < I[2]
      THEN \E p \in I[1]..(I[2] - 1) :
             \E t \in Partitions(I, p, seq) :
               /\ seq' = t
               /\ U' = (U \ {I}) \cup {<<I[1], p>>, <<p + 1, I[2]>>}
               /\ UNCHANGED seq0
      ELSE /\ U' = U \ {I}
           /\ UNCHANGED <<seq, seq0>>

Done ==
  /\ U = {}
  /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(U = {})

Sorted == \A i, j \in Indices : i < j => seq[i] <= seq[j]

PartialCorrectness == (U = {}) => Sorted
=============================================================================
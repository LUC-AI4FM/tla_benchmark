---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

VARIABLES seq, U

vars == <<seq, U>>

Indices == 1..N

(***************************************************************************)
(* Permutation helper: the set of all permutations of a finite set S,     *)
(* represented as bijections from S to S.                                  *)
(***************************************************************************)
Perms(S) == { f \in [S -> S] : \A w \in S : \E v \in S : f[v] = w }

(***************************************************************************)
(* All arrays obtained from B by permuting the elements whose indices are *)
(* in lo..hi, leaving elements outside lo..hi unchanged.                   *)
(***************************************************************************)
PermsOf(B, lo, hi) ==
  { [i \in Indices |-> IF i \in lo..hi THEN B[f[i]] ELSE B[i]] :
        f \in Perms(lo..hi) }

(***************************************************************************)
(* All valid partitions of B[lo..hi] around pivot p: every element at an  *)
(* index in lo..p is no greater than every element at an index in          *)
(* (p+1)..hi, and elements outside lo..hi are unchanged.                   *)
(***************************************************************************)
Partitions(B, p, lo, hi) ==
  { C \in PermsOf(B, lo, hi) :
        \A i \in lo..p : \A j \in (p+1)..hi : C[i] <= C[j] }

-----------------------------------------------------------------------------

TypeOK ==
  /\ seq \in [Indices -> 1..N]
  /\ U \subseteq (Indices \X Indices)

Init ==
  /\ seq \in [Indices -> 1..N]
  /\ U = { <<1, N>> }

(* An interval of length one or zero is simply removed. *)
Drop(I) ==
  /\ I[1] >= I[2]
  /\ U' = U \ {I}
  /\ UNCHANGED seq

(* An interval with more than one element is partitioned around a pivot. *)
Split(I) ==
  LET lo == I[1]
      hi == I[2]
  IN  /\ lo < hi
      /\ \E p \in lo..(hi - 1) :
            /\ seq' \in Partitions(seq, p, lo, hi)
            /\ U' = (U \ {I}) \cup { <<lo, p>>, <<p + 1, hi>> }

Terminated ==
  /\ U = {}
  /\ UNCHANGED vars

Next ==
  \/ \E I \in U : Drop(I) \/ Split(I)
  \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

Sorted(B) == \A i, j \in Indices : i < j => B[i] <= B[j]

PartialCorrectness == (U = {}) => Sorted(seq)

(* Liveness: the algorithm always eventually terminates. *)
Termination == <>(U = {})

THEOREM Spec => [](TypeOK /\ PartialCorrectness)
THEOREM Spec => Termination
=============================================================================
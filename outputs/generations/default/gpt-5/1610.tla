----------------------------- MODULE QuicksortPlusCal -----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
  Indices of the array and interval records
*)
Indices == 1..N

AllIntervals ==
  { [l |-> i, r |-> j] : i \in Indices, j \in i..N }

NontrivIntervals ==
  { iv \in AllIntervals : iv.l < iv.r }

(*
  Variables:
    A  : array as a function 1..N -> 1..N
    S  : set of intervals [l..r] (records with fields l, r) still to be processed
    pc : program counter with locations "qs1" and "Done"
*)
VARIABLES A, S, pc

vars == << A, S, pc >>

(*
  Bijection over a finite set S
*)
IsBijection(S, f) ==
  f \in [S -> S] /\ \A y \in S : \E! x \in S : f[x] = y

(*
  Set of subintervals to add after placing the pivot at position p in [l..r]
  Only nontrivial intervals (length >= 2) are kept.
*)
AddIntervals(l, r, p) ==
  (IF l < p-1 THEN { [l |-> l,     r |-> p-1] } ELSE {}) \cup
  (IF p+1 < r THEN { [l |-> p+1,   r |-> r  ] } ELSE {})

(*
  Partition step: Aprime is obtained by permuting A within [l..r],
  leaving A unchanged outside [l..r], placing the pivot value A[p] at p,
  and enforcing the usual partition ordering constraints around p.
*)
PartitionStep(Aold, Anew, l, r, p) ==
  LET Seg == l..r IN
  /\ \A i \in (Indices \ Seg) : Anew[i] = Aold[i]
  /\ \E f \in [Seg -> Seg] :
       /\ IsBijection(Seg, f)
       /\ \A i \in Seg : Anew[i] = Aold[f[i]]
  /\ LET pv == Aold[p] IN
       /\ Anew[p] = pv
       /\ \A i \in l..(p-1) : Anew[i] <= pv
       /\ \A i \in (p+1)..r : Anew[i] >= pv

(*
  Type correctness invariant
*)
TypeOK ==
  /\ pc \in {"qs1", "Done"}
  /\ A \in [Indices -> Indices]
  /\ S \subseteq NontrivIntervals

Init ==
  /\ pc = "qs1"
  /\ A \in [Indices -> Indices]
  /\ S = IF N >= 2 THEN { [l |-> 1, r |-> N] } ELSE {}

(*
  Single control-location action qs1.
  If S = {} then move to Done.
  Otherwise pick an interval iv = [l..r] in S, choose a pivot p in l..r,
  and nondeterministically replace A by a permutation that satisfies the
  partition constraints around p. Update S by removing iv and adding the
  nontrivial subintervals produced by p.
*)
qs1 ==
  /\ pc = "qs1"
  /\ IF S = {} THEN
       /\ pc' = "Done"
       /\ UNCHANGED << A, S >>
     ELSE
       \E iv \in S :
         LET l == iv.l
             r == iv.r IN
         \E p \in l..r :
         \E Aprime \in [Indices -> Indices] :
           /\ PartitionStep(A, Aprime, l, r, p)
           /\ A' = Aprime
           /\ S' = (S \ {iv}) \cup AddIntervals(l, r, p)
           /\ pc' = "qs1"

(*
  Terminal stuttering action
*)
Term ==
  /\ pc = "Done"
  /\ pc' = "Done"
  /\ UNCHANGED << A, S >>

Next == qs1 \/ Term

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

(*
  Safety invariant (can be checked under Spec)
*)
Invariant == TypeOK

(*
  Eventual termination property: the program counter eventually reaches "Done"
*)
Termination == Spec => <> (pc = "Done")
=============================================================================
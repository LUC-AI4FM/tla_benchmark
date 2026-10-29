------------------------------- MODULE FunctionalDigraphCycles -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* A functional digraph over a finite vertex set: each vertex has exactly  *)
(* one outgoing neighbour, given by a function f \in [Vertices -> Vertices]*)
(***************************************************************************)

Vertices == 1..3
Values   == 0..2
MaxSteps == 4

VARIABLES graph, cand, step

vars == <<graph, cand, step>>

(***************************************************************************)
(* (b) Range / image of a function over its finite domain                  *)
(***************************************************************************)
Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* k-fold iteration of f starting from v (terminates: k decreases)         *)
(***************************************************************************)
RECURSIVE Iterate(_, _, _)
Iterate(f, v, k) == IF k = 0 THEN v ELSE f[Iterate(f, v, k - 1)]

Orbit(f, v, n) == { Iterate(f, v, k) : k \in 0..(n - 1) }

(***************************************************************************)
(* (a) Simple directed cycle predicate                                     *)
(***************************************************************************)
IsSimpleCycle(S, f) ==
    LET n == Cardinality(S) IN
    /\ S # {}
    /\ S \subseteq DOMAIN f
    /\ \A v \in S : f[v] \in S
    /\ \A v \in S :
          /\ Iterate(f, v, n) = v
          /\ \A k \in 1..(n - 1) : Iterate(f, v, k) # v
          /\ Orbit(f, v, n) = S

\* Alternative (reference) characterisation: S can be enumerated without
\* repetition as p[1], ..., p[n] with f[p[k]] = p[(k % n) + 1].
IsBijection(p, D, R) ==
    /\ \A x \in D : p[x] \in R
    /\ \A x, y \in D : p[x] = p[y] => x = y
    /\ \A r \in R : \E x \in D : p[x] = r

CycleByEnumeration(S, f) ==
    LET n == Cardinality(S) IN
    /\ S # {}
    /\ \E p \in [1..n -> S] :
          /\ IsBijection(p, 1..n, S)
          /\ \A k \in 1..n : f[p[k]] = p[(k % n) + 1]

(***************************************************************************)
(* (c) Removing the element at position i from a finite sequence           *)
(***************************************************************************)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

RemoveAtSpec(s, i) ==
    [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

(***************************************************************************)
(* (d) Reduction of f[from..to] with binary associative op and base value  *)
(*     Terminates since (to - from) strictly decreases.                    *)
(***************************************************************************)
RECURSIVE Reduce(_, _, _, _, _)
Reduce(op(_, _), f, from, to, base) ==
    IF from > to THEN base
    ELSE op(Reduce(op, f, from, to - 1, base), f[to])

RECURSIVE FoldSeq(_, _, _)
FoldSeq(op(_, _), s, base) ==
    IF s = <<>> THEN base
    ELSE op(FoldSeq(op, SubSeq(s, 1, Len(s) - 1), base), s[Len(s)])

Add(a, b) == a + b

(***************************************************************************)
(* Bounded universe of sequences for checking                              *)
(***************************************************************************)
SeqsUpTo(n) == UNION { [1..k -> Values] : k \in 0..n }

(***************************************************************************)
(* Behaviour: explore graphs and candidate vertex sets                     *)
(***************************************************************************)
TypeOK ==
    /\ graph \in [Vertices -> Vertices]
    /\ cand \in SUBSET Vertices
    /\ step \in 0..MaxSteps

Init ==
    /\ graph \in [Vertices -> Vertices]
    /\ cand \in SUBSET Vertices
    /\ step = 0

Next ==
    /\ step < MaxSteps
    /\ \E v, w \in Vertices : graph' = [graph EXCEPT ![v] = w]
    /\ cand' \in SUBSET Vertices
    /\ step' = step + 1

Done == step = MaxSteps /\ UNCHANGED vars

Spec == Init /\ [][Next \/ Done]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Correctness invariants                                                  *)
(***************************************************************************)
CycleCorrect ==
    IsSimpleCycle(cand, graph) <=> CycleByEnumeration(cand, graph)

CycleClosed ==
    IsSimpleCycle(cand, graph) =>
        /\ \A v \in cand : graph[v] \in cand
        /\ Range([v \in cand |-> graph[v]]) = cand

RangeCorrect ==
    /\ \A y \in Range(graph) : \E x \in Vertices : graph[x] = y
    /\ \A x \in Vertices : graph[x] \in Range(graph)

RemoveAtCorrect ==
    \A s \in SeqsUpTo(3) : \A i \in 1..Len(s) :
        /\ Len(RemoveAt(s, i)) = Len(s) - 1
        /\ RemoveAt(s, i) = RemoveAtSpec(s, i)

ReduceCorrect ==
    \A s \in SeqsUpTo(3) :
        \A from \in 1..(Len(s) + 1) : \A to \in (from - 1)..Len(s) :
            Reduce(Add, s, from, to, 0) = FoldSeq(Add, SubSeq(s, from, to), 0)

ReduceBase ==
    \A s \in SeqsUpTo(2) : \A b \in Values :
        Reduce(Add, s, Len(s) + 1, Len(s), b) = b

Invariant ==
    /\ TypeOK
    /\ CycleCorrect
    /\ CycleClosed
    /\ RangeCorrect
    /\ RemoveAtCorrect
    /\ ReduceCorrect
    /\ ReduceBase

Termination == <>(step = MaxSteps)

=============================================================================================
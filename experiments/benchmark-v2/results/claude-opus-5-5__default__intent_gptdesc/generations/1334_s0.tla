------------------------------ MODULE FunctionalDigraphCycles ------------------------------
(***************************************************************************)
(* A functional digraph: every vertex has exactly one outgoing edge,       *)
(* given by a total function f \in [Vertices -> Vertices].                  *)
(*                                                                         *)
(* The model supports:                                                     *)
(*  (a) deciding whether a finite set S of vertices is a simple directed   *)
(*      cycle under f, both declaratively and by an explicit walk;         *)
(*  (b) computing the image (range) of a function on a finite domain;      *)
(*  (c) removing an element from a finite sequence;                        *)
(*  (d) reducing a range of sequence values with an associative operator   *)
(*      (sum) from an explicit base value, computed by an explicit loop.   *)
(*                                                                         *)
(* Safety invariants state the correctness properties. Loop invariants and *)
(* a decreasing variant justify termination on finite domains.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Vertices,   \* finite, nonempty set of vertices
    Values,     \* finite set of natural numbers used as sequence elements
    MaxLen      \* bound on the length of the sequences considered

ASSUME ConstantsOK ==
    /\ IsFiniteSet(Vertices)
    /\ Vertices # {}
    /\ IsFiniteSet(Values)
    /\ Values \subseteq Nat
    /\ MaxLen \in Nat

-----------------------------------------------------------------------------
(***************************************************************************)
(* Generic operators                                                       *)
(***************************************************************************)

\* (b) Image / range of a function over its (finite) domain
Range(g) == { g[x] : x \in DOMAIN g }

\* Bounded finite sequences over Values
BoundedSeqs == UNION { [1..n -> Values] : n \in 0..MaxLen }

\* n-fold application of g starting from x
RECURSIVE Iterate(_, _, _)
Iterate(g, x, n) == IF n = 0 THEN x ELSE g[Iterate(g, x, n - 1)]

\* Orbit of v under g, of length n (v, g[v], ..., g^(n-1)[v])
Orbit(g, v, n) == { Iterate(g, v, j) : j \in 0..(n - 1) }

\* f restricted to S
Restrict(g, S) == [ x \in S |-> g[x] ]

IsClosed(g, S) == \A v \in S : g[v] \in S

IsBijectionOn(h, S) ==
    /\ \A x \in S : h[x] \in S
    /\ \A x, y \in S : h[x] = h[y] => x = y
    /\ \A y \in S : \E x \in S : h[x] = y

(***************************************************************************)
(* (a) Simple cycle predicate (algorithmic form): every vertex of S        *)
(* returns to itself after exactly |S| steps and not earlier.             *)
(***************************************************************************)
IsSimpleCycle(g, S) ==
    /\ S # {}
    /\ IsClosed(g, S)
    /\ \A v \in S :
         /\ Iterate(g, v, Cardinality(S)) = v
         /\ \A j \in 1..(Cardinality(S) - 1) : Iterate(g, v, j) # v

(***************************************************************************)
(* Declarative characterization: closed under f, f|S a permutation of S,  *)
(* consisting of a single cycle whose length equals |S| (no repeats).     *)
(***************************************************************************)
SimpleCycleSpec(g, S) ==
    /\ S # {}
    /\ IsClosed(g, S)
    /\ IsBijectionOn(Restrict(g, S), S)
    /\ \E v \in S :
         /\ Orbit(g, v, Cardinality(S)) = S
         /\ Iterate(g, v, Cardinality(S)) = v

\* (c) Remove element at index i from sequence s
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

\* (d) Associative operator with explicit base value (identity)
Op(a, b) == a + b
Base == 0

\* Reduction over the index range lo..hi of s (left fold from Base)
RECURSIVE ReduceRange(_, _, _)
ReduceRange(s, lo, hi) ==
    IF hi < lo THEN Base ELSE Op(ReduceRange(s, lo, hi - 1), s[hi])

\* Repeated application of Op over a whole sequence
RECURSIVE FoldSeq(_)
FoldSeq(t) ==
    IF t = << >> THEN Base ELSE Op(FoldSeq(SubSeq(t, 1, Len(t) - 1)), t[Len(t)])

IsDistinctSeq(p) == \A i, j \in 1..Len(p) : i # j => p[i] # p[j]

-----------------------------------------------------------------------------
VARIABLES
    f,       \* the functional digraph
    S,       \* candidate cycle vertex set
    seq,     \* finite sequence of values
    rmIdx,   \* index to remove from seq
    lo, hi,  \* index range for the reduction
    acc,     \* reduction accumulator
    k,       \* reduction loop counter
    path,    \* walk along f from a vertex of S
    phase    \* "reduce" -> "walk" -> "done"

vars == << f, S, seq, rmIdx, lo, hi, acc, k, path, phase >>

TypeOK ==
    /\ f \in [Vertices -> Vertices]
    /\ S \in SUBSET Vertices
    /\ seq \in BoundedSeqs
    /\ rmIdx \in 1..(MaxLen + 1)
    /\ lo \in 1..(Len(seq) + 1)
    /\ hi \in (lo - 1)..Len(seq)
    /\ acc \in Nat
    /\ k \in lo..(hi + 1)
    /\ path \in Seq(Vertices)
    /\ phase \in {"reduce", "walk", "done"}

Init ==
    /\ f \in [Vertices -> Vertices]
    /\ S \in SUBSET Vertices
    /\ seq \in BoundedSeqs
    /\ rmIdx \in 1..(MaxLen + 1)
    /\ lo \in 1..(Len(seq) + 1)
    /\ hi \in (lo - 1)..Len(seq)
    /\ acc = Base
    /\ k = lo
    /\ path = IF S = {} THEN << >> ELSE << CHOOSE v \in S : TRUE >>
    /\ phase = "reduce"

Last(p) == p[Len(p)]

\* One step of the reduction loop
ReduceStep ==
    /\ phase = "reduce"
    /\ k <= hi
    /\ acc' = Op(acc, seq[k])
    /\ k' = k + 1
    /\ UNCHANGED << f, S, seq, rmIdx, lo, hi, path, phase >>

ReduceDone ==
    /\ phase = "reduce"
    /\ k > hi
    /\ phase' = "walk"
    /\ UNCHANGED << f, S, seq, rmIdx, lo, hi, acc, k, path >>

\* Follow f from the last vertex while no vertex repeats
WalkStep ==
    /\ phase = "walk"
    /\ path # << >>
    /\ f[Last(path)] \notin Range(path)
    /\ path' = Append(path, f[Last(path)])
    /\ UNCHANGED << f, S, seq, rmIdx, lo, hi, acc, k, phase >>

WalkDone ==
    /\ phase = "walk"
    /\ \/ path = << >>
       \/ f[Last(path)] \in Range(path)
    /\ phase' = "done"
    /\ UNCHANGED << f, S, seq, rmIdx, lo, hi, acc, k, path >>

Finished ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next == ReduceStep \/ ReduceDone \/ WalkStep \/ WalkDone \/ Finished

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Result of the explicit walk: S is a simple cycle iff the walk from a    *)
(* vertex of S closes back to its start, visiting exactly S.              *)
(***************************************************************************)
WalkResult ==
    /\ path # << >>
    /\ f[Last(path)] = path[1]
    /\ Range(path) = S
    /\ Len(path) = Cardinality(S)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* (a) The cycle predicate characterizes exactly the simple cycles
CycleCharacterization ==
    IsSimpleCycle(f, S) <=> SimpleCycleSpec(f, S)

\* (a') The explicit walk agrees with the predicate once it terminates
WalkCorrect ==
    phase = "done" => (WalkResult <=> IsSimpleCycle(f, S))

\* (b) Range computation returns exactly the images of domain elements
RangeCorrect ==
    /\ Range(f) = { y \in Vertices : \E x \in Vertices : f[x] = y }
    /\ Range(seq) = { y \in Values : \E i \in 1..Len(seq) : seq[i] = y }
    /\ \A y \in Range(f) : \E x \in DOMAIN f : f[x] = y

\* (c) Removal: length decreases by one and order of others is preserved
RemoveCorrect ==
    rmIdx \in 1..Len(seq) =>
        LET r == RemoveAt(seq, rmIdx) IN
        /\ Len(r) = Len(seq) - 1
        /\ \A j \in 1..Len(r) :
              r[j] = IF j < rmIdx THEN seq[j] ELSE seq[j + 1]
        /\ r = SubSeq(seq, 1, rmIdx - 1) \o SubSeq(seq, rmIdx + 1, Len(seq))

\* (d) Reduction is well-defined from the base value ...
ReduceBaseDefined ==
    /\ ReduceRange(seq, lo, lo - 1) = Base
    /\ FoldSeq(<< >>) = Base

\* ... and agrees with repeated application over the subsequence
ReduceMatchesFold ==
    ReduceRange(seq, lo, hi) = FoldSeq(SubSeq(seq, lo, hi))

\* Loop invariant for the reduction loop
ReduceLoopInv ==
    phase = "reduce" =>
        /\ k \in lo..(hi + 1)
        /\ acc = ReduceRange(seq, lo, k - 1)

\* Post-condition of the reduction loop
ReduceCorrect ==
    phase # "reduce" =>
        /\ k = hi + 1
        /\ acc = ReduceRange(seq, lo, hi)
        /\ acc = FoldSeq(SubSeq(seq, lo, hi))

\* Loop invariant for the walk
WalkLoopInv ==
    /\ (S = {}) <=> (path = << >>)
    /\ path # << >> => path[1] \in S
    /\ IsDistinctSeq(path)
    /\ \A i \in 1..(Len(path) - 1) : path[i + 1] = f[path[i]]
    /\ \A i \in 1..Len(path) : path[i] = Iterate(f, path[1], i - 1)
    /\ Len(path) <= Cardinality(Vertices)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Termination                                                             *)
(***************************************************************************)

Measure ==
    CASE phase = "reduce" -> (hi + 1 - k) + Cardinality(Vertices) + 2
      [] phase = "walk"   -> (Cardinality(Vertices) - Len(path)) + 1
      [] OTHER            -> 0

\* Every non-stuttering step strictly decreases the variant
VariantDecreases ==
    [][Measure' < Measure]_vars

\* Both loops terminate on finite domains
Termination == <>(phase = "done")

StaysDone == [](phase = "done" => [](phase = "done"))

Invariants ==
    /\ TypeOK
    /\ CycleCharacterization
    /\ WalkCorrect
    /\ RangeCorrect
    /\ RemoveCorrect
    /\ ReduceBaseDefined
    /\ ReduceMatchesFold
    /\ ReduceLoopInv
    /\ ReduceCorrect
    /\ WalkLoopInv

THEOREM Spec => []Invariants
THEOREM Spec => Termination
=============================================================================
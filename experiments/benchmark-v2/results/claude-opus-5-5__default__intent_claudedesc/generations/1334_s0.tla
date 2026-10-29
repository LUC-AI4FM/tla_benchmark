---------------------------- MODULE Utils ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Vals,      \* finite set of integer values used to build sequences
          MaxLen     \* bound on sequence length for model checking

ASSUME /\ Vals \subseteq Int
       /\ IsFiniteSet(Vals)
       /\ MaxLen \in Nat

VARIABLE seq

vars == <<seq>>

-----------------------------------------------------------------------------
(* Utility operators                                                       *)
-----------------------------------------------------------------------------

\* Aggregation: process f[from], f[from+1], ..., f[to] in order, combining
\* each element with the accumulated result, starting from base.
Reduce(op(_, _), f, from, to, base) ==
    IF to < from
    THEN base
    ELSE LET acc[i \in (from - 1)..to] ==
                 IF i < from THEN base ELSE op(f[i], acc[i - 1])
         IN acc[to]

\* Arithmetic helper usable as a combining function.
Add(a, b) == a + b

\* Sequence membership test.
InSeq(s, e) == \E i \in 1..Len(s) : s[i] = e

\* Remove the element at position i, preserving the order of the others.
Remove(s, i) ==
    [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

\* Range (image) of a function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Does r, viewed as a successor graph over S, form a simple cycle that
\* visits every element of S exactly once before returning to the start?
IsSimpleCycle(S, r) ==
    LET n == Cardinality(S)
        Iter[k \in 0..n] ==
            IF k = 0 THEN [x \in S |-> x]
                     ELSE [x \in S |-> r[Iter[k - 1][x]]]
    IN /\ DOMAIN r = S
       /\ \A x \in S : r[x] \in S
       /\ \A x \in S : {Iter[k][x] : k \in 1..n} = S
       /\ \A x \in S : Iter[n][x] = x

-----------------------------------------------------------------------------
(* A small driver system exercising the utilities                         *)
-----------------------------------------------------------------------------

Init == seq = <<>>

AppendElem ==
    /\ Len(seq) < MaxLen
    /\ \E v \in Vals : seq' = Append(seq, v)

RemoveElem ==
    /\ Len(seq) > 0
    /\ \E i \in 1..Len(seq) : seq' = Remove(seq, i)

Next == AppendElem \/ RemoveElem

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Invariants                                                              *)
-----------------------------------------------------------------------------

TypeOK == /\ seq \in Seq(Vals)
          /\ Len(seq) <= MaxLen

\* Reduction correctness: empty range yields base; each step combines the
\* next element with the accumulated result, in order.
ReduceCorrect ==
    /\ Reduce(Add, seq, 1, 0, 0) = 0
    /\ \A k \in 1..Len(seq) :
          Reduce(Add, seq, 1, k, 0) = Add(seq[k], Reduce(Add, seq, 1, k - 1, 0))

\* Removal preserves order of the remaining elements.
RemovePreservesOrder ==
    \A i \in 1..Len(seq) :
        LET t == Remove(seq, i)
        IN /\ Len(t) = Len(seq) - 1
           /\ \A j \in 1..(i - 1) : t[j] = seq[j]
           /\ \A j \in i..Len(t) : t[j] = seq[j + 1]

\* Membership agrees with range extraction.
MembershipConsistent ==
    \A v \in Vals : InSeq(seq, v) <=> v \in Range(seq)

\* Cycle completeness: a simple cycle over Vals covers all of Vals, and
\* following it from any start returns to the start after |Vals| steps.
CycleCompleteness ==
    \A f \in [Vals -> Vals] :
        IsSimpleCycle(Vals, f) =>
            /\ Range(f) = Vals
            /\ \A x \in Vals : f[x] # x \/ Cardinality(Vals) = 1

Invariants ==
    /\ TypeOK
    /\ ReduceCorrect
    /\ RemovePreservesOrder
    /\ MembershipConsistent
    /\ CycleCompleteness

=============================================================================
---- MODULE BalanceScalePuzzle ----
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS W, N

VARIABLES dummy

(*
  Helper: sum of first i elements of a sequence/function with domain 1..Len(s)
*)
RECURSIVE SumTo(_, _)
SumTo(s, i) ==
  IF i = 0 THEN 0
  ELSE SumTo(s, i - 1) + s[i]

SeqSum(s) == SumTo(s, Len(s))

(*
  Enumerate all non-decreasing sequences of length N of positive integers
  that sum to wt, extending the given prefix seq.
*)
RECURSIVE Partitions(_, _)
Partitions(seq, wt) ==
  LET k == Len(seq) IN
  LET rem == wt - SeqSum(seq) IN
  LET r == N - k IN
  IF r = 0 THEN
    IF rem = 0 THEN { seq } ELSE {}
  ELSE
    LET lb == IF k = 0 THEN 1 ELSE seq[k] IN
    LET ub == rem \div r IN
      UNION { Partitions(seq \o << x >>, wt) : x \in lb..ub }

(*
  Can target weight wt be represented as a signed combination of pieces in seq,
  with coefficients from {-1,0,1}?
*)
Weighs(seq, wt) ==
  \E f \in [1..Len(seq) -> {-1, 0, 1}]:
    SumTo([i \in 1..Len(seq) |-> f[i] * seq[i]], Len(seq)) = wt

Solutions ==
  { s \in Partitions(<< >>, W) : \A wt \in 1..W : Weighs(s, wt) }

(*
  Trivial state structure (no real state or transitions), as required.
*)
Init == dummy = 0
Next == UNCHANGED dummy
vars == << dummy >>
Spec == Init /\ [][Next]_vars

(*
  Basic assumptions on constants and the TLC-driven search/print harness.
  Override W and N in a TLC model if desired (defaults: W = 40, N = 4).
*)
ASSUME N \in Nat \ {0} /\ W \in Nat \ {0}

ASSUME
  LET sols == Solutions IN
  IF sols # {} THEN
    LET chosen == CHOOSE s \in sols : TRUE IN
      /\ PrintT("Solution") = "Solution"
      /\ PrintT(chosen) = chosen
  ELSE
      PrintT("No solution") = "No solution"

====
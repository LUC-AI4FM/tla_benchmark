------------------------------ MODULE BalanceScale ------------------------------
EXTENDS Integers, Naturals, Sequences, TLC

CONSTANTS W, N

(*
  Basic typing assumptions for TLC. Adjust W and N in the model configuration.
*)
ASSUME /\ W \in Nat \ {0}
       /\ N \in Nat \ {0}

Nat1 == Nat \ {0}

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF s = << >> THEN 0
  ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE Partitions(_, _)
Partitions(w, n) ==
  IF n = 0 THEN
    IF w = 0 THEN { << >> } ELSE {}
  ELSE
    UNION { { <<k>> \o t : t \in Partitions(w - k, n - 1) } : k \in 1..w }

CoeffSet == { -1, 0, 1 }

CoeffSeqs(n) == [1..n -> CoeffSet]

RECURSIVE ProdSeq(_, _)
ProdSeq(a, b) ==
  IF a = << >> THEN << >>
  ELSE << Head(a) * Head(b) >> \o ProdSeq(Tail(a), Tail(b))

WeightedSum(c, p) == SumSeq(ProdSeq(c, p))

BalancedFor(p, t) ==
  \E c \in CoeffSeqs(Len(p)) : WeightedSum(c, p) = t

Weighable(p) ==
  /\ p \in Partitions(W, N)
  /\ \A t \in 1..W : BalancedFor(p, t)

Solutions ==
  { p \in Partitions(W, N) : \A t \in 1..W : BalancedFor(p, t) }

OneSolution ==
  IF Solutions = {} THEN << >> ELSE CHOOSE s \in Solutions : TRUE

(*
  TLC-oriented search/print: evaluate this ASSUME to either show a solution
  or report that none exists for the given W and N.
*)
Search ==
  IF Solutions # {} THEN
    PrintT(<<"Solution found:", OneSolution>>)
  ELSE
    PrintT(<<"No solution exists for:", <<"W", W>>, <<"N", N>>>>)

ASSUME Search
===============================================================================
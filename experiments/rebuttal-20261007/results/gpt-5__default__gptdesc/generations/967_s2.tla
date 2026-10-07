---- MODULE BalanceScaleStoneCutting ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N

ASSUME W \in Nat /\ N \in Nat

VARIABLES stones

Nat1 == Nat \ {0}

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0
  ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE Partitions(_, _)
Partitions(total, n) ==
  IF n = 0 THEN
    IF total = 0 THEN {<< >>} ELSE {}
  ELSE IF total <= 0 THEN
    {}
  ELSE
    UNION { { Append(p, k) : p \in Partitions(total - k, n - 1) } : k \in 1..total }

RECURSIVE CoefSeqs(_)
CoefSeqs(n) ==
  IF n = 0 THEN {<< >>}
  ELSE UNION { { Append(c, k) : c \in CoefSeqs(n - 1) } : k \in {-1, 0, 1} }

DotProd(s, c) ==
  SumSeq([ i \in 1..Len(s) |-> c[i] * s[i] ])

CanWeigh(s, t) ==
  \E c \in CoefSeqs(Len(s)) : DotProd(s, c) = t

Weighable(s) ==
  \A t \in 1..W : CanWeigh(s, t)

Init ==
  LET S == { s \in Partitions(W, N) : Weighable(s) } IN
    stones = IF S = {} THEN << >> ELSE CHOOSE s \in S : TRUE

Next == UNCHANGED stones

Spec == Init /\ [][Next]_<<stones>>

(*
  Safety invariants for TLC to check:
  - TypeInv: either no solution (stones = << >>) or stones is an ordered partition of W into N positive naturals.
  - WeighInv: if a solution is chosen, it is weighable for all targets 1..W with coefficients in {-1,0,1}.
*)
TypeInv ==
  stones = << >> \/
  ( Len(stones) = N /\ \A i \in 1..N : stones[i] \in Nat1 /\ SumSeq(stones) = W )

WeighInv ==
  stones = << >> \/ Weighable(stones)

(*
  TLC-oriented ASSUME/PrintT search and reporting:
  - Prints the number of weighable ordered partitions.
  - Prints an example solution if one exists, otherwise reports that no solution exists.
*)
ASSUME
  LET S == { s \in Partitions(W, N) : Weighable(s) } IN
    PrintT(<<"Number of solutions:", Cardinality(S)>>) /\
    IF S # {} THEN
      PrintT(<<"Example solution:", CHOOSE s \in S : TRUE>>)
    ELSE
      PrintT("No solution exists for the given W and N")

====
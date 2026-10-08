---- MODULE BalancedScale ----
EXTENDS Naturals, Integers, Sequences, TLC

(*
  Constants:
    W = total weight (e.g., 40)
    N = number of pieces (e.g., 4)
*)
CONSTANTS W, N

(*
  Sum of a sequence of integers
*)
RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF s = << >> THEN 0 ELSE Head(s) + SumSeq(Tail(s))

(*
  Generator of all non-decreasing sequences of length k consisting of
  positive integers >= m that sum to t.
  Parts(k, m, t) returns a set of sequences.
*)
RECURSIVE Parts(_, _, _)
Parts(k, m, t) ==
  IF k = 0 THEN
    IF t = 0 THEN { << >> } ELSE {}
  ELSE
    UNION { { <<x>> \o s : s \in Parts(k - 1, x, t - x) } : x \in m..t }

(*
  All candidate ordered partitions: non-decreasing sequences of length N
  with positive integers summing to W.
*)
Candidates ==
  Parts(N, 1, W)

(*
  Sum of elementwise product of partition p (a sequence) and coefficients c.
*)
SumProd(p, c) ==
  SumSeq(ToSeq([ i \in 1..Len(p) |-> c[i] * p[i] ]))

(*
  CanMeasure(p, t): does there exist a {-1,0,1}-coefficient vector that
  yields signed sum t using pieces p?
*)
CanMeasure(p, t) ==
  \E c \in [ 1..Len(p) -> {-1, 0, 1} ] : SumProd(p, c) = t

(*
  A partition p is valid iff it can measure every integer weight 1..W.
*)
IsSolution(p) ==
  /\ Len(p) = N
  /\ SumSeq(p) = W
  /\ \A t \in 1..W : CanMeasure(p, t)

(*
  All valid solutions among the candidates.
*)
Solutions ==
  { p \in Candidates : IsSolution(p) }

(*
  When TLC evaluates this ASSUME, it prints either a found solution
  (as a sequence) or "No solution".
*)
PrintOutcome ==
  IF Solutions # {} THEN
    PrintT(<<"Solution", CHOOSE p \in Solutions : TRUE>>)
  ELSE
    PrintT("No solution")

ASSUME PrintOutcome

====
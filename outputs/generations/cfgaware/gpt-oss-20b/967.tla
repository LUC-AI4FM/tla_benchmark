------------------------------ MODULE StoneCut ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS W, N

(* ------------------------------------------------------------------ *)
(*  Partition(n,w)  -- all ordered partitions of w into n natural parts *)
(* ------------------------------------------------------------------ *)

Partition(n, w) ==
  IF n = 0 THEN
    IF w = 0 THEN {<>} ELSE {}
  ELSE
    { <k> ^ rest |
        k \in Nat /\ 1 <= k <= w
        /\ rest \in Partition(n-1, w-k)
      }

(* ------------------------------------------------------------------ *)
(*  SumSeq(seq)     -- sum of the elements of a sequence                *)
(* ------------------------------------------------------------------ *)

SumSeq(seq) ==
  IF seq = <> THEN 0
  ELSE Head(seq) + SumSeq(Tail(seq))

(* ------------------------------------------------------------------ *)
(*  WeightedSum(coeffs, seq)  -- weighted sum with coefficients in {-1,0,1} *)
(* ------------------------------------------------------------------ *)

WeightedSum(coeffs, seq) ==
  IF Len(coeffs) = Len(seq) THEN
    SUM i \in 1..Len(seq): coeffs[i] * seq[i]
  ELSE 0

(* ------------------------------------------------------------------ *)
(*  Balanced(seq)   -- every weight 1..W can be represented using seq   *)
(* ------------------------------------------------------------------ *)

Balanced(seq) ==
  \A t \in 1..W :
    \E coeffs \in Seq({-1,0,1}) :
      Len(coeffs) = Len(seq)
      /\ WeightedSum(coeffs, seq) = t

(* ------------------------------------------------------------------ *)
(*  Search for a solution and print it                                 *)
(* ------------------------------------------------------------------ *)

ASSUME
  \E sol \in Partition(N,W) : Balanced(sol)
THEN
  PrintT("Solution: ", sol)
ELSE
  PrintT("No solution")

END MODULE
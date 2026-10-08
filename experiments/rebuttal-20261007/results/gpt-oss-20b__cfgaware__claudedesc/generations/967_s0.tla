------------------------------ MODULE CarTalkPuzzle ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N

(* Partitions operator *)
Partitions(n, w) ==
  IF n = 0 THEN
    IF w = 0 THEN {<>} ELSE {}
  ELSE
    { a \cat seq' :
      a \in 1..(w \div n) /\
      seq' \in Partitions(n-1, w-a) /\
      (\A x \in seq' : x >= a) }

(* Weighs operator *)
Weighs(seq, wt) ==
  \E coeffs \in [1..Len(seq)] -> {-1,0,1} :
    Sum i \in 1..Len(seq) : coeffs[i] * seq[i] = wt

ASSUME
  (\E seq \in Partitions(N, W) :
      (\A w \in 1..W : Weighs(seq, w)) /\ PrintT("Solution: ", seq))
  \/ PrintT("No solution")

=============================================================================
------------------------------ MODULE WeighingPieces ------------------------------

EXTENDS Naturals, Integers, Sequences

(*
  Parameters:
    W : total weight (positive integer)
    N : number of pieces (positive integer)
*)
CONSTANTS W, N

ASSUME W \in Nat \ {0} /\ N \in Nat \ {0}

VARIABLES Pieces

Domain == 1..N

(*
  Sum of a sequence of integers
*)
RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumSeq(Tail(s))

ToSeq(f) == [i \in Domain |-> f[i]]
TotalPieces(f) == SumSeq(ToSeq(f))

(*
  Symmetry-breaking to consider only partitions (order does not matter).
  Nondecreasing sequence of piece weights.
*)
Nondecreasing(f) == \A i \in 1..(N-1): f[i] <= f[i+1]

(*
  Coefficients for placements: -1 (right pan), 0 (unused), 1 (left pan)
*)
CoeffSet == {-1, 0, 1}

Dot(c, p) == SumSeq([i \in Domain |-> c[i] * p[i]])

(*
  Achievability of a target t: there exists a placement producing net t
*)
Achieves(t) ==
  \E c \in [Domain -> CoeffSet]:
    Dot(c, Pieces) = t

AchievesAllTargets ==
  \A t \in 1..W: Achieves(t)

(*
  Basic typing and structural properties
*)
TypeOK == Pieces \in [Domain -> Nat]

PositivePieces == \A i \in Domain: Pieces[i] \in Nat \ {0}

SumIsW == TotalPieces(Pieces) = W

PartitionOrder == Nondecreasing(Pieces)

PiecesFormMultiset == /\ PositivePieces /\ SumIsW

(*
  Specification: a single static state satisfying the partition constraints.
*)
Init ==
  /\ TypeOK
  /\ PositivePieces
  /\ SumIsW
  /\ PartitionOrder

Next == UNCHANGED <<Pieces>>

Spec == Init /\ [][Next]_<<Pieces>>

==============================
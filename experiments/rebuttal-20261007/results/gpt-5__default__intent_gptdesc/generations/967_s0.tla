------------------------------ MODULE WeighingPieces ------------------------------

EXTENDS Naturals, Integers

CONSTANTS W, N

ASSUME /\ N \in Nat \ {0}
       /\ W \in Nat \ {0}

Nat1 == Nat \ {0}
Idx == 1..N
Targets == 1..W
CoeffSet == {-1, 0, 1}

RECURSIVE SumFrom(_,_)
SumFrom(m, f) ==
  IF m = 0 THEN 0
  ELSE SumFrom(m - 1, f) + f[m]

PiecesSum(p) == SumFrom(N, p)

Nondecreasing(p) == \A i \in 1..(N - 1): p[i] <= p[i + 1]

LinComb(p, c) == SumFrom(N, [i \in Idx |-> c[i] * p[i]])

AllTargetsAchievable(p) ==
  \A t \in Targets:
    \E c \in [Idx -> CoeffSet]: LinComb(p, c) = t

VARIABLES Pieces

Init ==
  /\ Pieces \in [Idx -> Nat1]
  /\ Nondecreasing(Pieces)
  /\ PiecesSum(Pieces) = W

Next == UNCHANGED Pieces

vars == << Pieces >>

Spec == Init /\ [][Next]_vars

(*
  Safety invariants to check
*)
PositiveInv == \A i \in Idx: Pieces[i] \in Nat1
PartitionInv == PiecesSum(Pieces) = W
CanonicalInv == Nondecreasing(Pieces)
AllTargetsAchievableInv == AllTargetsAchievable(Pieces)

=============================================================================
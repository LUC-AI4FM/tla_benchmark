------------------------------ MODULE WeighingPieceDesign ------------------------------
EXTENDS Integers

CONSTANTS W, N

VARIABLES pieces

CoeffSet == [1..N -> {-1,0,1}]

Achieves(t) ==
  ∃c \in CoeffSet : (SUM i \in 1..N : c[i] * pieces[i]) = t

AllTargetsAchievable ==
  ∀t \in 1..W : Achieves(t)

Init ==
  /\ pieces \in [1..N -> Nat]
  /\ (SUM i \in 1..N : pieces[i]) = W
  /\ AllTargetsAchievable

Next == UNCHANGED <<pieces>>

Spec == Init /\ [][Next]_<<pieces>>

Invariant ==
  /\ (SUM i \in 1..N : pieces[i]) = W
  /\ ∀i \in 1..N : pieces[i] > 0

THEOREM PartitionInvariant == [] (Spec => Invariant)

THEOREM AllTargetsAchievableTheorem == [] (Spec => AllTargetsAchievable)
END WeighingPieceDesign
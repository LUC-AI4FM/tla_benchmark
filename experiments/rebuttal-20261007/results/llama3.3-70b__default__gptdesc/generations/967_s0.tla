```tla
MODULE BalanceScale

EXTENDS Integers, Sequences

CONSTANTS W, N

VARIABLES pieces, targetWeight

Init ==
  /\ pieces = <<>>
  /\ targetWeight = 1

Next ==
  /\ IF targetWeight <= W THEN
      /\ pieces' = Append(pieces, CHOOSE w \in Nat \ {0} : w <= W)
      /\ targetWeight' = targetWeight + 1
    ELSE
      /\ pieces' = pieces
      /\ targetWeight' = targetWeight
  /\ PrintT("pieces", pieces)

Spec ==
  Init /\ [][Next]_<<pieces, targetWeight>>

THEOREM Spec => []<>(targetWeight = W + 1)
```
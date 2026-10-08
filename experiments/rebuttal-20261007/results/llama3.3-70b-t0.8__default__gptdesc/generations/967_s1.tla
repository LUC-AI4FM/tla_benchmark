```tla
MODULE BalanceScale
EXTENDS Integers, Sequences

CONSTANTS W, N

VARIABLES pieces, target, coefficients, sum

Init ==
  /\ pieces = <<>>
  /\ target = 1
  /\ coefficients = <<>>
  /\ sum = 0

Next ==
  /\ IF target <= W
    THEN
      /\ IF \E p \in Nat & p <= W & Len(pieces) < N
        THEN
          /\ pieces' = Append(pieces, p)
          /\ target' = target + 1
          /\ coefficients' = <<>>
          /\ sum' = 0
        ELSE
          /\ IF \E c \in {-1, 0, 1}
            THEN
              /\ coefficients' = Append(coefficients, c)
              /\ sum' = sum + c * pieces[Len(coefficients)]
              /\ target' = IF sum' = target THEN target + 1 ELSE target
              /\ pieces' = pieces
            ELSE
              /\ pieces' = <<>>
              /\ target' = 1
              /\ coefficients' = <<>>
              /\ sum' = 0
      ELSE
        /\ pieces' = pieces
        /\ target' = target
        /\ coefficients' = coefficients
        /\ sum' = sum

Spec ==
  Init /\ [][Next]_<<pieces, target, coefficients, sum>>

THEOREM Spec => [](\E p \in Nat & p <= W & Len(pieces) = N)
ASSUME W > 0
ASSUME N > 0

PrintT == 
  IF \E p \in Nat & p <= W & Len(pieces) = N
  THEN "Solution found: " ++ SeqToString(pieces)
  ELSE "No solution exists"

Fairness == SF_VARIABLES(pieces)

=============================================================================
```
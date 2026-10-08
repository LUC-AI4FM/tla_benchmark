```tla
MODULE BalanceScale

EXTENDS Integers, Sequences

CONSTANTS W, N

VARIABLES pieces, targetWeight, coefficients

Init ==
  /\ pieces = <<>>
  /\ targetWeight = 1
  /\ coefficients = <<>>

Next ==
  \/ TargetWeightIncrement
  \/ PieceAppend
  \/ CoefficientUpdate

TargetWeightIncrement ==
  /\ targetWeight < W
  /\ pieces' = pieces
  /\ targetWeight' = targetWeight + 1
  /\ coefficients' = coefficients

PieceAppend ==
  /\ pieces # <<>>
  /\ targetWeight' = targetWeight
  /\ pieces' = Append(pieces, 1)
  /\ coefficients' = coefficients

CoefficientUpdate ==
  /\ pieces # <<>>
  /\ targetWeight' = targetWeight
  /\ pieces' = pieces
  /\ coefficients' = coefficients
  /\ \E c \in {-1, 0, 1} : 
    (coefficients' = Append(coefficients, c))

Spec == Init /\ [][Next]_<<pieces, targetWeight, coefficients>>

THEOREM Spec => []<>(targetWeight = W)

Fairness == SF_VARIABLES(pieces) /\ WF_VARIABLES(targetWeight) /\ SF_VARIABLES(coefficients)

ASSUME W > 0
ASSUME N > 0

PrintT == 
  IF pieces # <<>> THEN 
    LET sum == Sum(coefficients) IN
      IF sum = targetWeight THEN
        PrintT("Solution found: " + SeqToString(pieces))
      ELSE 
        PrintT("No solution exists")
  ELSE 
    PrintT("No solution exists")

Sum(seq) == IF seq = <<>> THEN 0 ELSE Head(seq) + Sum(Tail(seq))

SeqToString(seq) == 
  IF seq = <<>> THEN "" 
  ELSE (Str(Head(seq)) + ", " + SeqToString(Tail(seq)))
```
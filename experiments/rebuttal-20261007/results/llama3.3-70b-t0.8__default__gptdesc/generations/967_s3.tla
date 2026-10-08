```tla
MODULE BalanceScale

EXTENDS Integers, TLC

CONSTANTS W, N

VARIABLES weights, targetWeight

Init ==
  /\ weights = <<>>
  /\ targetWeight = 1

Next ==
  /\ IF targetWeight <= W THEN
      /\ weights' = Append(weights, CHOOSE w \in Nat \ {0} : TRUE)
      /\ targetWeight' = targetWeight + 1
    ELSE
      /\ weights' = weights
      /\ targetWeight' = targetWeight
  /\ PrintT(<<"weights: ", weights>>)

Spec ==
  Init /\ [][Next]_weights

Balance(weightSeq, target) ==
  \E coeffs \in Seq(-1..1, Length(weightSeq)) :
    SumProduct(coeffs, weightSeq) = target

SumProduct(seq, weights) ==
  IF seq = <<>> THEN
    0
  ELSE
    Head(seq) * Head(weights) + SumProduct(Tail(seq), Tail(weights))

Inv ==
  \A i \in 1..Length(weights) :
    Balance(SubSeq(weights, 1, i), targetWeight)

THEOREM Spec => []Inv

ASSUME W > 0 /\ N > 0

Fairness == SF_VARIABLES

```
Note: The provided TLA+ module assumes that TLC (the Temporal Logic Checker for TLA+) will be used to model-check and explore the state space defined by this specification. The `PrintT` statement is specific to TLC's model checking and is used here to display potential solutions as the model checker explores the state space.
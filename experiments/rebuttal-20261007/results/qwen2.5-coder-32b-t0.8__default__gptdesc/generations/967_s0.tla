```tla
MODULE BalanceScale

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES pieces

Init == pieces = <<>>

Next ==
  \/ /\ Len(pieces) < N
     /\ \E w \in {1..W - Sum(pieces)} : pieces' = Append(pieces, w)
  \/ /\ Len(pieces) = N
     /\ pieces' = pieces

Spec == Init /\ [][Next]_<<pieces>>

Sum(s) == IF s = <<>> THEN 0 ELSE Head(s) + Sum(Tail(s))

CanMeasure(target) ==
  LET Coefficients(seq) == {c \in [1..Len(pieces) -> {-1, 0, 1}]}
      Measure(c)       == Sum(<< FORALL i \in DOMAIN c : pieces[i] * c[i] >>)
  IN  \E c \in Coefficients(pieces) : Measure(c) = target

SafetyInvariant == /\ Len(pieces) <= N
                   /\ \A i \in 1..Len(pieces) : pieces[i] > 0
                   /\ Sum(pieces) <= W

LivenessProperty ==
  \/ \A target \in {1..W} : CanMeasure(target)
  \/ PrintT("No solution exists")

SpecWithSafety == Spec /\ []SafetyInvariant

FairnessAssumption == WF_next(<<pieces>>)

CompleteSpec == SpecWithSafety /\ LivenessProperty /\ FairnessAssumption
```
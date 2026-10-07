MODULE NegInitTest
EXTENDS Integers

VARIABLE s

Init ==
  ∃ v \in {0,1} : (s = v /\ v < 1)

Next ==
  s' = s

Inv == s < 1

Spec ==
  Init /\ [] (Next) /\ Inv
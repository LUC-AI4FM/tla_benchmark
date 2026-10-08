---------------------------- MODULE HigherOrderDemo ----------------------------
EXTENDS Integers, TLC

CONSTANT None

VARIABLE x

FilterSet(s, unaryPred, binaryPred) ==
  {e \in s : unaryPred(e) /\ binaryPred(e)}

Init ==
  x = FilterSet({1, 2, 3, 4, 5}, 
                λ e : e > 1,
                λ e : (e % 2 = 1) ∧ TRUE)

Next == FALSE
=============================================================================
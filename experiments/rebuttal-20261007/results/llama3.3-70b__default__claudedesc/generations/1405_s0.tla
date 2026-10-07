```tla
MODULE SimpleTwoVariableSystem
EXTENDS Integers, Sequences, TLC
INSTANCE Inner725f WITH res = outerRes, myseq = outerSeq

CONSTANTS 

VARIABLES outerRes, outerSeq

Init == (outerSeq = <<1, 2, 3>>) ∧ (outerRes = 0)

Next == Svc!Step ∨ (outerRes' = outerRes) ∧ (outerSeq' = outerSeq)

Svc!Step == (outerRes = 0) ∧ (outerRes' = 1) ∧ 
             (outerSeq' = [x \in outerSeq | x ≠ 1])

Spec == Init ∧ [][Next]_<<outerRes, outerSeq>> ∧ Svc!Fairness

Svc!Fairness == WF_(Svc!Step)

SpecRunsToEnd == Spec ∧ ◇[](¬Enabled(Svc!Step))

Enabled(Svc!Step) == ∃ x \in outerSeq : (outerRes = 0)
```
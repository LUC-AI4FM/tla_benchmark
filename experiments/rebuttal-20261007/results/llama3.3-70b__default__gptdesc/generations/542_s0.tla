```
MODULE SimplePlusCal
EXTENDS Integers

CONSTANTS ProcA, ProcB
VARIABLES x, pc

Init == (x = 0) ∧ (pc = <<"Start", "Start">>)

Next == \/ (pc[ProcA] = "Start") ∧ (pc' = [pc EXCEPT ![ProcA] = "Done"]) ∧ (x' = x + 1)
        \/ (pc[ProcB] = "Start") ∧ (pc' = [pc EXCEPT ![ProcB] = "Done"]) ∧ (x' = x + 1)
        \/ (pc[ProcA] = "Done") ∧ (pc[ProcB] = "Done") ∧ (pc' = pc) ∧ (x' = x)

Spec == Init ∧ [][Next]_<<pc, x>>
Termination == <>((pc[ProcA] = "Done") ∧ (pc[ProcB] = "Done"))

THEOREM Spec => Termination
```
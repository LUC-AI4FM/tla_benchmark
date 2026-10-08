---------------------------- MODULE IncrementingProcesses ----------------------------
EXTENDS Integers

VARIABLE x, pc

Init == (x = 0) ∧ (pc = [ProcA |-> "Start", ProcB |-> "Start"])

a == (pc[ProcA] = "Start") ∧ (x' = x + 1) ∧ (pc' = [pc EXCEPT !ProcA = "Done"])
b == (pc[ProcB] = "Start") ∧ (x' = x + 1) ∧ (pc' = [pc EXCEPT !ProcB = "Done"])

Terminating == (pc[ProcA] = "Done") ∧ (pc[ProcB] = "Done") ∧ (x' = x) ∧ (pc' = pc)

Next == IF (pc[ProcA] = "Start") ∨ (pc[ProcB] = "Start") THEN a ∨ b ELSE Terminating

Spec == Init ∧ [][Next]_<<x, pc>>
=============================================================================
------------------------------ MODULE FastMutexSpec ------------------------------
EXTENDS Naturals

CONSTANTS N, M

VARIABLES x, y, b, phase

vars == <<x, y, b, phase>>

Init ==
   /\ x = 0
   /\ y = FALSE
   /\ b = FALSE
   /\ phase = [i \in 1..N |-> 0]

ClassA(i) == i <= M
ClassB(i) == i > M

TryA(i) ==
   /\ phase[i] = 0
   /\ phase' = [phase EXCEPT ![i] = 1]
   /\ x' = i
   /\ y' = FALSE

EnterA(i) ==
   /\ phase[i] = 1
   /\ b = FALSE
   /\ IF x = i THEN
        (b' = TRUE /\ phase' = [phase EXCEPT ![i] = 2])
      ELSE
        (y = FALSE /\ b' = TRUE /\ phase' = [phase EXCEPT ![i] = 2])

ExitA(i) ==
   /\ phase[i] = 2
   /\ phase' = [phase EXCEPT ![i] = 0]
   /\ y' = TRUE
   /\ b' = FALSE

TryB(i) ==
   /\ phase[i] = 0
   /\ phase' = [phase EXCEPT ![i] = 1]
   /\ y' = FALSE
   /\ x' = i

EnterB(i) == EnterA(i)

ExitB(i) == ExitA(i)

AAction(i) == TryA(i) \/ EnterA(i) \/ ExitA(i)
BAction(i) == TryB(i) \/ EnterB(i) \/ ExitB(i)

Next ==
   ∨_{i \in 1..N} (
        (ClassA(i) /\ AAction(i))
        \/ (ClassB(i) /\ BAction(i))
   )

Spec ==
   Init
   /\ [][Next]_vars
   /\ ∀ i \in 1..M : WF_vars(AAction(i))
   /\ ∀ i \in (M+1)..N : WF_vars(BAction(i))

Invariant ==
   ∀ i, j \in 1..N :
      i ≠ j => ~(phase[i] = 2 /\ phase[j] = 2)

Liveness ==
   ∃ i \in 1..N : [] ◊ (phase[i] = 2)

============================================================================
----------------------------- MODULE FairSequentialCounter -----------------------------

EXTENDS Naturals, Integers

CONSTANT N
ASSUME N = 10

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = "Loop"

Inc ==
  /\ pc = "Loop"
  /\ x < N
  /\ x' = x + 1
  /\ pc' = "Loop"

Finish ==
  /\ pc = "Loop"
  /\ x >= N
  /\ UNCHANGED x
  /\ pc' = "Done"

Next == Inc \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInv == x \in Nat
BoundsInv == x \in 0..N
PcInv == pc \in {"Loop", "Done"}
Inv == TypeInv /\ BoundsInv /\ PcInv

Termination == <>(pc = "Done")

AtFive == x = 5
FinishLoop == (pc = "Done") /\ (x = N)
PossibleCounts == [ state \in {"Loop", "Done"} |-> IF state = "Loop" THEN 0..N ELSE {N} ]

========================================================================================
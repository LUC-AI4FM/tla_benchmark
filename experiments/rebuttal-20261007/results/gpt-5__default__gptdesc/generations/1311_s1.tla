----------------------------- MODULE GCDLoop -----------------------------

EXTENDS Integers, Naturals

VARIABLES u, v, v0, pc

vars == << u, v, v0, pc >>

RECURSIVE GCD(_, _)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ v0 = v
  /\ pc = "Loop"

Swap ==
  /\ pc = "Loop"
  /\ u # 0
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ UNCHANGED v0
  /\ pc' = "Loop"

Sub ==
  /\ pc = "Loop"
  /\ u # 0
  /\ u >= v
  /\ u' = u - v
  /\ v' = v
  /\ UNCHANGED v0
  /\ pc' = "Loop"

DoneStep ==
  /\ pc = "Loop"
  /\ u = 0
  /\ UNCHANGED << u, v, v0 >>
  /\ pc' = "Done"

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Swap \/ Sub \/ DoneStep \/ Stutter

Spec == /\ Init /\ [][Next]_vars

TypeInv ==
  /\ u \in Nat
  /\ v \in Nat \ {0}
  /\ v0 \in 1..50
  /\ pc \in {"Loop", "Done"}

GCDInv == GCD(u, v) = GCD(24, v0)

TerminatedGCD == (pc = "Done") => v = GCD(24, v0)

============================================================================
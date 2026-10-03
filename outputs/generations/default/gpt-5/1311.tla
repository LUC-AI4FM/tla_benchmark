----------------------------- MODULE GCDLoop -----------------------------

EXTENDS Integers

CONSTANTS U0, VMax

ASSUME U0 = 24 /\ VMax = 50

VARIABLES u, v, v0, pc

vars == << u, v, v0, pc >>

RangeV == 1..VMax

Divides(d, n) == ∃ k \in Nat : n = d * k

CommonDivisors(a, b) ==
  { d \in Nat : d > 0 /\ Divides(d, a) /\ Divides(d, b) }

GCD(a, b) ==
  CHOOSE g \in CommonDivisors(a, b) :
    ∀ h \in CommonDivisors(a, b) : h <= g

Init ==
  /\ u = U0
  /\ v \in RangeV
  /\ v0 = v
  /\ pc = "Loop"

Loop ==
  /\ pc = "Loop"
  /\ pc' = IF u = 0 THEN "Done"
          ELSE IF u < v THEN "Swap"
          ELSE "Sub"
  /\ UNCHANGED << u, v, v0 >>

Swap ==
  /\ pc = "Swap"
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ v0' = v0
  /\ pc' = "Loop"

Sub ==
  /\ pc = "Sub"
  /\ u > 0
  /\ u >= v
  /\ u' = u - v
  /\ v' = v
  /\ v0' = v0
  /\ pc' = "Loop"

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Loop \/ Swap \/ Sub \/ Done

Spec == /\ Init /\ [][Next]_vars

(*
  Safety invariants and properties
*)
TypeOK ==
  /\ u \in Nat
  /\ v \in RangeV
  /\ v0 \in RangeV
  /\ pc \in {"Loop", "Swap", "Sub", "Done"}

GCDInvariant == GCD(u, v) = GCD(U0, v0)

DoneZero == (pc = "Done") => u = 0

DoneCorrect == (pc = "Done") => v = GCD(U0, v0)

=============================================================================
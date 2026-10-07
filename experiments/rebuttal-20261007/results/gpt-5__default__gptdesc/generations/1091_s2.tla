--------------------------- MODULE PCR ---------------------------

EXTENDS Naturals

CONSTANTS P0, D0, T0, H0

ASSUME P0 \in Nat /\ D0 \in Nat /\ T0 \in Nat /\ H0 \in Nat

VARIABLES phase, temp, P, D, T, H

PhaseSet == {"Heating", "Cooling", "Annealing", "Extension"}
TempSet  == {"High", "Low"}

Min2(a, b) == IF a <= b THEN a ELSE b

vars == << phase, temp, P, D, T, H >>

Init ==
  /\ phase = "Heating"
  /\ temp  = "High"
  /\ P = P0
  /\ D = D0
  /\ T = T0
  /\ H = H0

Heating ==
  /\ phase = "Heating"
  /\ phase' = "Cooling"
  /\ temp'  = "High"
  /\ P' = P
  /\ H' = H
  /\ T' = T + 2 * D
  /\ D' = 0

Cooling ==
  /\ phase = "Cooling"
  /\ phase' = "Annealing"
  /\ temp'  = "Low"
  /\ UNCHANGED << P, D, T, H >>

Annealing ==
  /\ phase = "Annealing"
  /\ phase' = "Extension"
  /\ temp'  = "Low"
  /\ \E k \in 0..Min2(P, T):
       /\ P' = P - k
       /\ T' = T - k
       /\ H' = H + k
       /\ D' = D

Extension ==
  /\ phase = "Extension"
  /\ phase' = "Heating"
  /\ temp'  = "Low"
  /\ \E e \in 0..H:
       /\ P' = P
       /\ T' = T
       /\ H' = H - e
       /\ D' = D + e

Next == Heating \/ Cooling \/ Annealing \/ Extension

TypeOK ==
  /\ phase \in PhaseSet
  /\ temp  \in TempSet
  /\ P \in Nat /\ D \in Nat /\ T \in Nat /\ H \in Nat

Count0 == P0 + T0 + 2 * (H0 + D0)

CountPreserved == P + T + 2 * (H + D) = Count0

Spec == Init /\ [][Next]_vars

Safety == TypeOK /\ CountPreserved

LivenessPrimerDepletion == <> (P = 0)

=================================================================